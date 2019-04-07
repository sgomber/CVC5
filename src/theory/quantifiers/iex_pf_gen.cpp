/*********************                                                        */
/*! \file iex_pf_gen.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of instantiation explain proof generalization
 **/

#include "theory/quantifiers/iex_pf_gen.h"

#include "options/quantifiers_options.h"
#include "proof/uf_proof.h"
#include "theory/quantifiers/inst_explain_db.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

InstExplainPfGen::InstExplainPfGen(InstExplainDb& parent, QuantifiersEngine* qe)
    : d_ied(parent), d_qe(qe), d_ev(parent.d_ev)
{
  d_false = NodeManager::currentNM()->mkConst(false);
  d_true = NodeManager::currentNM()->mkConst(true);
}

void InstExplainPfGen::reset(Theory::Effort e)
{
  // do nothing
}

void InstExplainPfGen::indent(const char* c, unsigned tb)
{
  for (unsigned i = 0; i < tb; i++)
  {
    Trace(c) << " ";
  }
}

bool InstExplainPfGen::regressExplain(EqExplainer* eqe,
                                      std::vector<TNode>& assumptions,
                                      eq::EqProof* eqp)
{
  if (eqp->d_id == eq::MERGED_THROUGH_EQUALITY)
  {
    // use the explainer
    if (eqe)
    {
      Assert(!eqp->d_node.isNull());
      Trace("ied-proof-debug") << "Explain: " << eqp->d_node << std::endl;
      if (!eqe->explain(eqp->d_node, assumptions, eqp))
      {
        Trace("ied-proof-debug")
            << "FAILED to explain " << eqp->d_node << std::endl;
        return false;
      }
      Trace("ied-proof-debug") << "...success" << std::endl;
      return true;
    }
    Trace("ied-proof-debug") << "FAILED to explain " << eqp->d_node
                             << " (no explainer)" << std::endl;
    return false;
  }
  for (unsigned i = 0, nchild = eqp->d_children.size(); i < nchild; i++)
  {
    if (!regressExplain(eqe, assumptions, eqp->d_children[i].get()))
    {
      return false;
    }
  }
  return true;
}

Node InstExplainPfGen::generalize(
    eq::EqProof* eqp,
    std::map<eq::EqProof*, Node>& concs,
    std::map<eq::EqProof*, std::map<Node, GLitInfo>>& concsg,
    unsigned tb)
{
  std::map<eq::EqProof*, Node>::iterator itc = concs.find(eqp);
  if (itc != concs.end())
  {
    return itc->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  // what kind of proof?
  Node ret;
  if (Trace.isOn("ied-gen"))
  {
    indent("ied-gen", tb);
  }
  unsigned id = eqp->d_id;
  if (id == eq::MERGED_THROUGH_CONGRUENCE)
  {
    // FIXME
    return Node::null();
    Node cnode = eqp->d_node;
    Trace("ied-gen") << "ied-pf: congruence node(" << cnode << ")" << std::endl;
    // get child proofs
    std::vector<eq::EqProof*> childProofs;
    eq::EqProof* curr = eqp;
    do
    {
      Assert(curr->d_children.size() == 2);
      childProofs.push_back(curr->d_children[1].get());
      curr = curr->d_children[0].get();
    } while (curr->d_id == eq::MERGED_THROUGH_CONGRUENCE);
    unsigned nchild = cnode.getNumChildren();
    if (childProofs.size() == nchild)
    {
      bool success = true;
      std::vector<Node> rhsArgs;
      if (cnode.getMetaKind() == metakind::PARAMETERIZED)
      {
        rhsArgs.push_back(cnode.getOperator());
      }
      Node retc;
      for (unsigned i = 0; i < nchild; i++)
      {
        // child proofs are stored in reverse order since congruence proofs
        // are left associative.
        unsigned ii = nchild - (i + 1);
        retc = generalize(childProofs[ii], concs, concsg, tb + 1);
        if (retc.isNull())
        {
          success = false;
          break;
        }
        unsigned matchIndex;
        if (getMatchIndex(retc, cnode[i], matchIndex))
        {
          rhsArgs.push_back(retc[1 - matchIndex]);
        }
        else
        {
          success = false;
          break;
        }
      }
      if (success)
      {
        Kind k = cnode.getKind();
        Node cnodeEq = nm->mkNode(k, rhsArgs);
        ret = cnode.eqNode(cnodeEq);
      }
    }
    else
    {
      Debug("ied-gen-error") << "Unexpected (cong children):" << std::endl;
      eqp->debug_print("ied-gen-error", 1);
    }
  }
  else if (id == eq::MERGED_THROUGH_EQUALITY)
  {
    // an assumption
    ret = eqp->d_node;
    Assert(ret == Rewriter::rewrite(ret));
    Trace("ied-gen") << "ied-pf: equality " << ret << std::endl;
    // try to generalize here
    std::map<Node, InstExplainLit>::iterator itl;
    if (d_ied.findInstExplainLit(ret, itl))
    {
      InstExplainLit& iel = itl->second;
      // activate the literal
      d_ied.activateLit(ret);
      std::vector<Node>& cexp = iel.d_curr_insts;
      std::vector<Node>& colits = iel.d_curr_olits;
      Assert(cexp.size() == colits.size());
      for (unsigned i = 0, size = cexp.size(); i < size; i++)
      {
        Node pinst = cexp[i];
        // get the original literal
        Node olit = colits[i];
        Node colit = convertEq(olit);
        // initialize the generalization with the backwards mapping to its
        // concretization
        GLitInfo& gli = concsg[eqp][colit];
        if (Trace.isOn("ied-gen"))
        {
          indent("ied-gen", tb + 1);
          Trace("ied-gen") << "ied-pf: inst-explain equality " << olit
                           << std::endl;
          indent("ied-gen", tb + 1);
          Trace("ied-gen") << "        from " << pinst << std::endl;
        }
        // we must inst-explain it now
        if (!instExplain(gli, olit, ret, pinst, "ied-gen", tb + 2))
        {
          concsg[eqp].erase(colit);
          Trace("ied-gen") << "...failed" << std::endl;
        }
        else
        {
          Trace("ied-gen") << "...success!" << std::endl;
        }
      }
    }
    if (Trace.isOn("ied-gen"))
    {
      if (concsg.find(eqp) == concsg.end())
      {
        indent("ied-gen", tb + 1);
        Trace("ied-gen") << "ied-pf: no generalizations (tried "
                         << itl->second.d_curr_insts.size() << ")" << std::endl;
      }
    }
    ret = convertEq(ret);
  }
  else if (id == eq::MERGED_THROUGH_REFLEXIVITY)
  {
    // do nothing
    Node n = eqp->d_node;
    ret = n.eqNode(n);
    Trace("ied-gen") << "ied-pf: refl node(" << n << ")" << std::endl;
    // we do not care about generalizations here
  }
  else if (id == eq::MERGED_THROUGH_CONSTANTS)
  {
    //???
    Trace("ied-gen") << "ied-pf: constants ???" << std::endl;
    AlwaysAssert(false);
  }
  else if (id == eq::MERGED_THROUGH_TRANS)
  {
    // FIXME
    return Node::null();
    Trace("ied-gen") << "ied-pf: transitivity" << std::endl;
    bool success = true;
    Node retc;
    Node r1, r2;
    for (unsigned i = 0, nproofs = eqp->d_children.size(); i < nproofs; i++)
    {
      eq::EqProof* epi = eqp->d_children[i].get();
      retc = generalize(epi, concs, concsg, tb + 1);
      if (retc.isNull())
      {
        success = false;
        break;
      }
      else if (i == 0)
      {
        r1 = retc[0];
        r2 = retc[1];
      }
      else
      {
        unsigned matchIndex;
        if (getMatchIndex(retc, r1, matchIndex))
        {
          r1 = retc[1 - matchIndex];
        }
        else if (getMatchIndex(retc, r2, matchIndex))
        {
          r2 = retc[1 - matchIndex];
        }
        else
        {
          success = false;
          break;
        }
        // FIXME: merge generalizations
      }
    }
    if (success)
    {
      ret = r1.eqNode(r2);
    }
  }
  Assert(ret.getKind() == EQUAL);
  concs[eqp] = ret;
  if (Trace.isOn("ied-gen"))
  {
    indent("ied-gen", tb);
    Trace("ied-gen") << "...proves " << ret;
    std::map<eq::EqProof*, std::map<Node, GLitInfo>>::iterator itg =
        concsg.find(eqp);
    if (itg != concsg.end())
    {
      Trace("ied-gen") << ", with " << itg->second.size()
                       << " generalizations:" << std::endl;
      for (const std::pair<Node, GLitInfo>& p : itg->second)
      {
        indent("ied-gen", tb);
        Trace("ied-gen") << p.first << std::endl;
      }
    }
    else
    {
      Trace("ied-gen") << std::endl;
    }
  }
  return ret;
}

bool InstExplainPfGen::instExplain(
    GLitInfo& g, Node olit, Node lit, Node inst, const char* c, unsigned tb)
{
  if (Trace.isOn(c))
  {
    indent(c, tb);
    Trace(c) << "INST-EXPLAIN: " << lit << " / " << olit << std::endl;
    indent(c, tb);
    Trace(c) << "         from " << inst << std::endl;
  }
  InstExplainInst& iei = d_ied.getInstExplainInst(inst);
  // Since the instantiation lemma inst is propagating lit, we have that:
  //   inst { lit -> false }
  // must evaluate to false in the current context.
  // Node instExp = iei.getExplanationFor(lit);

  std::vector<Node> plits;
  std::vector<Node> plitso;
  // Second, get the SAT literals from inst that are propagating lit.
  // These literals are such that the propositional entailment holds:
  //   inst ^ plits[0] ^ ... ^ plits[k] |= lit
  if (!iei.justify(d_ev, lit, olit, plits, plitso))
  {
    if (Trace.isOn(c))
    {
      indent(c, tb);
      Trace(c) << "INST-EXPLAIN FAIL: (error) could not compute Boolean "
                  "propagation for "
               << lit << std::endl;
    }
    // if this fails, our computation of what Boolean propagates was wrong
    Assert(false);
    return false;
  }
  Assert(plits.size() == plitso.size());

  // For each literal in plits, we must either regress it further, or add it to
  // the assumptions of g.
  Node q = iei.getQuantifiedFormula();
  for (unsigned k = 0, plsize = plits.size(); k < plsize; k++)
  {
    Node pl = plits[k];
    Node opl = plitso[k];
    Assert(pl == Rewriter::rewrite(pl));
    if (Trace.isOn(c))
    {
      indent(c, tb + 1);
      Trace(c) << "inst-exp: requires " << pl << std::endl;
      indent(c, tb + 1);
    }
    // Now, regress the proof of pl / opl. It is either:
    // - the quantified formula itself, in which case it is an assumption,
    // - it is inst-explanable via a successful call to instExplainFind,
    // - it is an open leaf via a failed call to instExplainFind, in which
    // case it must be a conclusion.
    if( pl==q )
    {
      // if pl is the quantified formula for inst, we add it to assumptions
      Trace(c) << "-> which is the quantified formula, add to assumptions"
                << std::endl;
      g.d_assumptions.push_back(pl);
    }    
    // If its not the quantified formula, we try to find an inst-explanation
    else if (!instExplainFind(g, opl, pl, inst, c, tb))
    {
      // if we didn't find one, we must carry it must be a conclusion
      Trace(c) << "-> which has no inst-explanations, it must be a conclusion"
                << std::endl;
      g.d_conclusions[pl][opl].initialize(&iei);
    }
  }
  if (Trace.isOn(c))
  {
    indent(c, tb);
    Trace(c) << "INST-EXPLAIN SUCCESS with:" << std::endl;
    g.debugPrint(c, tb + 1);
  }
  return true;
}

bool InstExplainPfGen::instExplainFind(
    GLitInfo& g, Node opl, Node pl, Node instSrc, const char* c, unsigned tb)
{
  std::map<Node, InstExplainLit>::iterator itl;
  if (!d_ied.findInstExplainLit(pl, itl))
  {
    return false;
  }
  InstExplainLit& iel = itl->second;
  // Activate the literal. This computes whether any instantiation lemmas
  // are currently propagating it.
  d_ied.activateLit(pl);
  std::vector<Node>& cexppl = iel.d_curr_insts;
  std::vector<Node>& olitspl = iel.d_curr_olits;
  Assert(cexppl.size() == olitspl.size());
  if (Trace.isOn(c))
  {
    indent(c, tb + 1);
    Trace(c) << "  generalizes to " << opl << std::endl;
    indent(c, tb + 1);
    Trace(c) << "  and has " << cexppl.size() << " possible inst-explanations"
             << std::endl;
  }
  if (cexppl.empty())
  {
    indent(c, tb + 1);
    return false;
  }
  // populate choices for the proof regression, which we store in
  // g.d_conclusions[pl]
  std::map< Node, GLitInfo >& pconcs = g.d_conclusions[pl];
  // the current best explanation
  Node best;
  for (unsigned j = 0, cexpsize = cexppl.size(); j < cexpsize; j++)
  {
    Node instpl = cexppl[j];
    Node opli = olitspl[j];
    // The instantiation lemma that propagates pl should not be the same
    // as the one that propagates lit. Otherwise our computation of
    // Boolean propagation was wrong.
    Assert(instpl != instSrc);

    // check the matching constraints on opli against the original literal
    // in the quantified formula here.
    if (Trace.isOn(c))
    {
      indent(c, tb + 2);
      Trace(c) << "inst-exp: try " << opli << "..." << std::endl;
      indent(c, tb + 2);
    }
    // currently: we avoid matching constraints altogether by only
    // pursuing generalizations that are fully compatible with the
    // current.
    if (!g.checkCompatible(opl, opli))
    {
      Trace(c) << "  ...incompatible!" << std::endl;
    }
    else
    {
      Trace(c) << "  ...compatible, recurse" << std::endl;
      // recurse
      if (instExplain(pconcs[opli], opli, pl, instpl, c, tb + 3))
      {
        // if it is purely general, we are done
        if( pconcs[opli].d_conclusions.empty() )
        {
          best = opli;
          break;
        }
        else
        {
          // otherwise, it has a propagating generalization, take it.
          // we may carry this forward if all siblings are purely general.
          best = opli;
        }
      }
      else
      {
        // undo
        pconcs.erase(opli);
      }
    }
  }
  // now, take the best generalization if there are any available
  if (pconcs.empty())
  {
    g.d_conclusions.erase(pl);
    if (Trace.isOn(c))
    {
      indent(c, tb + 1);
      Trace(c) << "-> failed to generalize" << std::endl;
      indent(c, tb + 1);
    }
    return false;
  }
  Assert( !best.isNull() );
  Assert( pconcs.find(best)!=pconcs.end() );
  if (Trace.isOn(c))
  {
    indent(c, tb + 1);
    Trace(c) << "-> CHOOSE to merge " << best << std::endl;
    indent(c, tb + 1);
  }
  // merge the current with the child
  bool mergeSuccess = g.merge(opl, best, pconcs[best]);
  // remove the conclusions
  g.d_conclusions.erase(pl);
  if (!mergeSuccess)
  {
    if (Trace.isOn(c))
    {
      Trace(c) << "...failed to merge choice" << std::endl;
      indent(c, tb + 1);
    }
    return false;
  }
  Trace(c) << "...success" << std::endl;
  return true;
}

bool InstExplainPfGen::getMatchIndex(Node eq, Node n, unsigned& index)
{
  if (eq.isNull())
  {
    return false;
  }
  Assert(eq.getKind() == EQUAL);
  for (unsigned i = 0; i < 2; i++)
  {
    if (eq[i] == n)
    {
      index = i;
      return true;
    }
  }

  return false;
}

Node InstExplainPfGen::convertEq(Node n) const
{
  Kind k = n.getKind();
  if (k == EQUAL)
  {
    return n;
  }
  else if (k == NOT)
  {
    return n.eqNode(d_false);
  }
  Assert(n.getType().isBoolean());
  return n.eqNode(d_true);
}

Node InstExplainPfGen::convertRmEq(Node n) const
{
  Assert(n.getKind() == EQUAL);
  if (n[1] == d_true)
  {
    return n[0];
  }
  else if (n[1] == d_false)
  {
    n[0].negate();
  }
  return n;
}

bool InstExplainPfGen::isGeneralization(Node n, Node gn)
{
  // TODO
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
