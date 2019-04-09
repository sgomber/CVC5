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
Node InstExplainPfGen::generalize(Node tgtLit,
                                  eq::EqProof* eqp,
                                  std::map<eq::EqProof*, Node>& concs,
                                  std::map<eq::EqProof*, GLitInfo>& concsg,
                                  unsigned tb)
{
  std::map<Node, bool> genPath;
  return generalizeInternal(tgtLit, eqp, concs, concsg, genPath, tb);
}

Node InstExplainPfGen::generalizeInternal(
    Node tgtLit,
    eq::EqProof* eqp,
    std::map<eq::EqProof*, Node>& concs,
    std::map<eq::EqProof*, GLitInfo>& concsg,
    std::map<Node, bool>& genPath,
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
        retc = generalizeInternal(
            d_null, childProofs[ii], concs, concsg, genPath, tb + 1);
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
    if (Trace.isOn("ied-gen"))
    {
      Trace("ied-gen") << "ied-pf: equality " << ret << std::endl;
      indent("ied-gen", tb);
      Trace("ied-gen") << "INST-EXPLAIN find (UF leaf): " << ret << " / "
                       << tgtLit << std::endl;
    }
    bool recSuccess = instExplainFind(
        concsg[eqp], tgtLit, ret, Node::null(), genPath, "ied-gen", tb + 2);
    if (Trace.isOn("ied-gen"))
    {
      indent("ied-gen", tb);
    }
    if (recSuccess)
    {
      Trace("ied-gen") << "...success!" << std::endl;
    }
    else
    {
      concsg.erase(eqp);
      Trace("ied-gen") << "...failed to IEX UF leaf " << ret << " / " << tgtLit
                       << std::endl;
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
      // target literal is unknown if non-trivial
      Node tgtLitc = nproofs == 1 ? tgtLit : d_null;
      retc = generalizeInternal(tgtLitc, epi, concs, concsg, genPath, tb + 1);
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
    Trace("ied-gen") << "...proves " << ret << std::endl;
    /*
    std::map<eq::EqProof*, GLitInfo>::iterator itg =
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
    */
  }
  return ret;
}

// TODO: can focus assume vs conclusion
bool InstExplainPfGen::instExplain(GLitInfo& g,
                                   Node olit,
                                   Node lit,
                                   Node inst,
                                   std::map<Node, bool>& genPath,
                                   const char* c,
                                   unsigned tb)
{
  if (Trace.isOn(c))
  {
    indent(c, tb);
    Trace(c) << "INST-EXPLAIN: " << lit << " / " << olit << std::endl;
    indent(c, tb);
    Trace(c) << "from " << inst << std::endl;
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

  // If any literal is already being explored on this path, we have a cyclic
  // proof. We abort here since a cyclic proof cannot contribute to the
  // overall strength of the generalization, since its open leaves are
  // at least as weak as its root.
  for (const Node& pl : plits)
  {
    if (genPath.find(pl) != genPath.end() || pl == lit)
    {
      if (Trace.isOn(c))
      {
        indent(c, tb);
        Trace(c) << "INST-EXPLAIN FAIL: cycle found for premise " << pl
                 << std::endl;
      }
      return false;
    }
  }
  // indicate that we are exploring the generalized proof of lit.
  Assert(genPath.find(lit) == genPath.end());
  genPath[lit] = true;

  // For each literal in plits, we must either regress it further, or add it to
  // the assumptions of g.
  Node q = iei.getQuantifiedFormula();
  // the child with the UPG
  Node upgLit;
  Node upgOLit;
  for (unsigned k = 0, plsize = plits.size(); k < plsize; k++)
  {
    Node pl = plits[k];
    Node opl = plitso[k];
    Assert(pl == Rewriter::rewrite(pl));
    if (Trace.isOn(c))
    {
      indent(c, tb + 1);
      Trace(c) << "Premise #" << (k + 1) << ": " << pl << std::endl;
    }
    // Now, regress the proof of pl / opl. It is either:
    // - the quantified formula itself, in which case it is an assumption,
    // - it is inst-explanable via a successful call to instExplainFind,
    // - it is an open leaf via a failed call to instExplainFind, in which
    // case it must be a conclusion.
    bool isOpen = true;
    if (pl == q)
    {
      // if pl is the quantified formula for inst, we add it to assumptions
      if (Trace.isOn(c))
      {
        indent(c, tb + 1);
        Trace(c) << "-> quantified formula, add to assumptions" << std::endl;
      }
      g.d_assumptions.push_back(pl);
      isOpen = false;
    }
    // If its not the quantified formula, we try to find an inst-explanation
    else if (instExplainFind(g, opl, pl, inst, genPath, c, tb))
    {
      if (Trace.isOn(c))
      {
        indent(c, tb + 1);
      }
      // if we succeeded, then check if we are purely general
      if (g.isOpen(pl))
      {
        // if not, then we set the upgLit if we are the unique open branch
        if (g.d_conclusions.size() == 1)
        {
          Trace(c) << "-> inst-explained containing UPG" << std::endl;
          upgLit = pl;
          upgOLit = opl;
          isOpen = false;
        }
        else
        {
          Trace(c) << "-> inst-explained containing propagating "
                      "generalization, but not unique:"
                   << std::endl;
          g.debugPrint(c, tb + 1);
          // Already have another open branch, discard the generalization.
          // We reset this to a basic open leaf under "isOpen".
          g.d_conclusions.erase(pl);
        }
      }
      else
      {
        Trace(c) << "-> inst-explained, fully general" << std::endl;
        isOpen = false;
      }
    }
    else if (Trace.isOn(c))
    {
      indent(c, tb + 1);
      Trace(c) << "-> no inst-explanations" << std::endl;
    }
    if (isOpen)
    {
      Assert(g.d_conclusions.find(pl) == g.d_conclusions.end());
      // if we didn't find one, we must carry it must be a conclusion
      g.d_conclusions[pl][opl].initialize(&iei);
      // if we already had a UPG, discard it now and move here
      if (!upgLit.isNull())
      {
        g.d_conclusions.erase(upgLit);
        g.d_conclusions[upgLit][upgOLit].initialize(&iei);
        if (Trace.isOn(c))
        {
          indent(c, tb + 1);
          Trace(c) << "-> revert UPG " << upgLit << std::endl;
        }
      }
    }
  }
  if (Trace.isOn(c))
  {
    indent(c, tb);
    Trace(c) << "INST-EXPLAIN SUCCESS with:" << std::endl;
    g.debugPrint(c, tb + 1);
  }
  // clean up the path
  genPath.erase(lit);
  return true;
}

bool InstExplainPfGen::instExplainFind(GLitInfo& g,
                                       Node opl,
                                       Node pl,
                                       Node inst,
                                       std::map<Node, bool>& genPath,
                                       const char* c,
                                       unsigned tb)
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
    Trace(c) << "generalizes to " << opl << std::endl;
    indent(c, tb + 1);
    Trace(c) << "and has " << cexppl.size() << " possible inst-explanations"
             << std::endl;
  }
  if (cexppl.empty())
  {
    return false;
  }
  Assert(!opl.isNull());
  // populate choices for the proof regression, which we store in
  // g.d_conclusions[pl]
  std::map<Node, GLitInfo>& pconcs = g.d_conclusions[pl];
  // the (generalized) literal whose proof was the best
  Node best;
  // we proceed into two phases:
  // (1) Find an IEX inference whose generalized literal (opli below)
  // generalizes our target (opl), and whose proof is purely general,
  // (2) If not possible, find an IEX inference whose generalized literal
  // is generalized by opl and whose proof contains a UPG.
  //
  // opl may be null in the case where we are looking to establish
  // a generalization of a literal in UF proof with no inferrable target.
  // In this case, we take all IEX inferences regardless of whether
  // they are purely general.
  for (unsigned r = 0; r < 2; r++)
  {
    for (unsigned j = 0, cexpsize = cexppl.size(); j < cexpsize; j++)
    {
      Node instpl = cexppl[j];
      Node opli = olitspl[j];
      // The instantiation lemma that propagates pl should not be the same
      // as the one that propagates lit. Otherwise our computation of
      // Boolean propagation was wrong.
      Assert(instpl != inst);
      if (Trace.isOn(c))
      {
        indent(c, tb + 2);
        Trace(c) << "inst-exp: try " << opli << "..." << std::endl;
        indent(c, tb + 2);
      }
      // check the matching constraints on opli against the original literal
      // in the quantified formula opl here.
      // currently: we avoid matching constraints altogether by only
      // pursuing generalizations that are fully compatible with the
      // current.
      bool doRec = false;
      if (opl.isNull())
      {
        doRec = (r == 1);
      }
      else
      {
        doRec = g.checkCompatible(r == 0 ? opl : opli, r == 0 ? opli : opl);
      }
      if (doRec)
      {
        Trace(c) << "  ...compatible, recurse, phase="
                 << (r == 0 ? "assume" : "conclude") << std::endl;
        // recurse now
        bool undoOpli = true;
        if (instExplain(pconcs[opli], opli, pl, instpl, genPath, c, tb + 3))
        {
          if (opl.isNull())
          {
            // Don't have criteria to judge what is best, due to incomparable
            // matching.
            // TODO: could do subsumption to prune here
            undoOpli = false;
          }
          else if (pconcs[opli].d_conclusions.empty())
          {
            // if it is purely general, we are done
            if (r == 0)
            {
              best = opli;
              break;
            }
          }
          else if (r == 1)
          {
            // otherwise, it has a propagating generalization, take it.
            // we may carry this forward if all siblings are purely general.
            best = opli;
            break;
          }
        }
        if (undoOpli)
        {
          // undo this conclusion
          pconcs.erase(opli);
        }
      }
      else
      {
        Trace(c) << "  ...incompatible" << std::endl;
      }
    }
    // found one that met the criteria
    if (!best.isNull())
    {
      break;
    }
  }
  // TODO: search for instantiations that would have propagated this??

  // now, take the best generalization if there are any available
  if (pconcs.empty())
  {
    // we no longer have a valid conclusion, remove it
    g.d_conclusions.erase(pl);
    if (Trace.isOn(c))
    {
      indent(c, tb + 1);
      Trace(c) << "-> failed to generalize" << std::endl;
    }
    return false;
  }
  Assert(!best.isNull());
  Assert(pconcs.find(best) != pconcs.end());
  if (opl.isNull())
  {
    // we leave multiple possible conclusions here
    return true;
  }
  if (Trace.isOn(c))
  {
    indent(c, tb + 1);
    Trace(c) << "CHOOSE to set conclusion " << best << std::endl;
    indent(c, tb + 1);
  }
  // Set the conclusion to the one on child "best".
  // This will merge it into the parent if it has no open leaves.
  bool setSuccess = g.setConclusion(pl, best);
  if (!setSuccess)
  {
    // should never happen: pl / best should be a child in g.
    Assert(false);
    // remove it
    g.d_conclusions.erase(pl);
    if (Trace.isOn(c))
    {
      Trace(c) << "-> failed to set conclusion" << std::endl;
      indent(c, tb + 1);
    }
    return false;
  }
  // either purely general or has a UPG under pl
  Assert(!g.isOpen(pl) || g.d_conclusions[pl].size() == 1);
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
