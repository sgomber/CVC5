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

void InstExplainPfGen::reset(Theory::Effort e) { d_instFindPure.clear(); }

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
      Trace("iex-proof-debug") << "Explain: " << eqp->d_node << std::endl;
      if (!eqe->explain(eqp->d_node, assumptions, eqp))
      {
        Trace("iex-proof-debug")
            << "FAILED to explain " << eqp->d_node << std::endl;
        return false;
      }
      Trace("iex-proof-debug") << "...success" << std::endl;
      return true;
    }
    Trace("iex-proof-debug") << "FAILED to explain " << eqp->d_node
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
bool InstExplainPfGen::generalize(IexOutput& iout,
                                  Node tgtLit,
                                  eq::EqProof* eqp,
                                  IexProof& g,
                                  bool reqPureGen,
                                  unsigned tb)
{
  bool genSuccess = false;
  std::map<Node, bool> genPath;
  std::map<eq::EqProof*, Node> concs;
  generalizeInternal(
      iout, tgtLit, eqp, g, concs, reqPureGen, genPath, genSuccess, tb);
  return genSuccess;
}

Node InstExplainPfGen::generalizeInternal(IexOutput& iout,
                                          Node tgtLit,
                                          eq::EqProof* eqp,
                                          IexProof& g,
                                          std::map<eq::EqProof*, Node>& concs,
                                          bool reqPureGen,
                                          std::map<Node, bool>& genPath,
                                          bool& genSuccess,
                                          unsigned tb)
{
  std::map<eq::EqProof*, Node>::iterator itc = concs.find(eqp);
  if (itc != concs.end())
  {
    // TODO: carry generalized proof?
    return itc->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  // what kind of proof?
  Node ret;
  if (Trace.isOn("iex-gen"))
  {
    indent("iex-gen", tb);
  }
  unsigned id = eqp->d_id;
  if (id == eq::MERGED_THROUGH_CONGRUENCE)
  {
    // FIXME
    return Node::null();
    Node cnode = eqp->d_node;
    Trace("iex-gen") << "iex-pf: congruence node(" << cnode << ")" << std::endl;
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
        retc = generalizeInternal(iout,
                                  d_null,
                                  childProofs[ii],
                                  g,  // FIXME
                                  concs,
                                  reqPureGen,
                                  genPath,
                                  genSuccess,
                                  tb + 1);
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
      Debug("iex-gen-error") << "Unexpected (cong children):" << std::endl;
      eqp->debug_print("iex-gen-error", 1);
    }
  }
  else if (id == eq::MERGED_THROUGH_EQUALITY)
  {
    // an assumption
    ret = eqp->d_node;
    Assert(ret == Rewriter::rewrite(ret));
    if (Trace.isOn("iex-gen"))
    {
      Trace("iex-gen") << "iex-pf: equality " << ret << std::endl;
      indent("iex-gen", tb);
      Trace("iex-gen") << "INST-EXPLAIN find (UF leaf): " << ret << " / "
                       << tgtLit << std::endl;
    }
    genSuccess = instExplainFind(iout,
                                 g,
                                 tgtLit,
                                 ret,
                                 Node::null(),
                                 genPath,
                                 reqPureGen,
                                 "iex-gen",
                                 tb + 2);
    if (Trace.isOn("iex-gen"))
    {
      indent("iex-gen", tb);
    }
    if (genSuccess)
    {
      Trace("iex-gen") << "...success!" << std::endl;
    }
    else
    {
      Trace("iex-gen") << "...failed to IEX UF leaf " << ret << " / " << tgtLit
                       << std::endl;
    }
    ret = convertEq(ret);
  }
  else if (id == eq::MERGED_THROUGH_REFLEXIVITY)
  {
    // do nothing
    Node n = eqp->d_node;
    ret = n.eqNode(n);
    Trace("iex-gen") << "iex-pf: refl node(" << n << ")" << std::endl;
    // we do not care about generalizations here
  }
  else if (id == eq::MERGED_THROUGH_CONSTANTS)
  {
    // FIXME
    return Node::null();
    //???
    Trace("iex-gen") << "iex-pf: constants ???" << std::endl;
    AlwaysAssert(false);
  }
  else if (id == eq::MERGED_THROUGH_TRANS)
  {
    // FIXME
    return Node::null();
    Trace("iex-gen") << "iex-pf: transitivity" << std::endl;
    bool success = true;
    Node retc;
    Node r1, r2;
    for (unsigned i = 0, nproofs = eqp->d_children.size(); i < nproofs; i++)
    {
      eq::EqProof* epi = eqp->d_children[i].get();
      // target literal is unknown if non-trivial
      Node tgtLitc = nproofs == 1 ? tgtLit : d_null;
      retc = generalizeInternal(iout,
                                tgtLitc,
                                epi,
                                g,
                                concs,
                                reqPureGen,
                                genPath,
                                genSuccess,
                                tb + 1);
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
  if (Trace.isOn("iex-gen"))
  {
    indent("iex-gen", tb);
    Trace("iex-gen") << "...proves " << ret;
    if (tgtLit.isNull())
    {
      Trace("iex-gen") << " with no target.";
    }
    else
    {
      Trace("iex-gen") << " with target " << tgtLit << ", generalize success=";
      Trace("iex-gen") << genSuccess;
    }
    Trace("iex-gen") << std::endl;
  }
  return ret;
}

bool InstExplainPfGen::instExplain(IexOutput& iout,
                                   IexProof& g,
                                   Node olit,
                                   Node lit,
                                   Node inst,
                                   std::map<Node, bool>& genPath,
                                   bool reqPureGen,
                                   const char* c,
                                   unsigned tb)
{
  Assert(g.empty());
  if (Trace.isOn(c))
  {
    indent(c, tb);
    Trace(c) << "INST-EXPLAIN: " << lit << " / " << olit
             << (reqPureGen ? " (PURE)" : "") << std::endl;
    indent(c, tb);
    Trace(c) << "from " << inst << std::endl;
  }
  // check if cached
  std::map<Node, Node>::iterator itp = d_instFindPure.find(olit);
  if (itp != d_instFindPure.end())
  {
    if (!itp->second.isNull())
    {
      g.d_assumptions.push_back(itp->second);
      return true;
    }
    else if (reqPureGen)
    {
      // we only fail if we indeed require purely general here
      return false;
    }
  }

  InstExplainInst& iei = d_ied.getInstExplainInst(inst);
  g.initialize(&iei);
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
    // if this fails, we may have had a "circular explanation" of a propagation.
    // this can occur if we are using a tautological instantiation lemma.
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
      Trace(c) << "Premise #" << (k + 1) << ": " << pl << " for " << olit
               << std::endl;
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
    // If its not the quantified formula, we try to find an inst-explanation.
    // We require a pure generalization if we already set a propagating
    // generalization.
    else if (instExplainFind(iout,
                             g,
                             opl,
                             pl,
                             inst,
                             genPath,
                             reqPureGen || !upgLit.isNull(),
                             c,
                             tb))
    {
      isOpen = g.isOpen(pl);
    }
    else if (Trace.isOn(c))
    {
      indent(c, tb + 1);
      Trace(c) << "-> no inst-explanations" << std::endl;
    }
    if (isOpen)
    {
      if (reqPureGen)
      {
        if (Trace.isOn(c))
        {
          indent(c, tb);
          Trace(c) << "INST-EXPLAIN FAIL (PURE): no purely general proof for "
                   << pl << std::endl;
        }
        d_instFindPure[olit] = Node::null();
        // clean up path
        genPath.erase(lit);
        // clear everything since we failed (not necessary)
        // g.initialize(nullptr);
        return false;
      }
    }
  }
  if (Trace.isOn(c))
  {
    indent(c, tb);
    Trace(c) << "INST-EXPLAIN SUCCESS " << olit << " "
             << (reqPureGen ? "(PURE)" : "") << " with:" << std::endl;
    g.debugPrint(c, tb + 1);
  }
  if (reqPureGen)
  {
    Assert(g.isPurelyGeneral());
    d_instFindPure[olit] = g.getAssumptions();
    // was this non-trivial? If so, we compress the proof and remember the
    // lemma.
    // if (!plits.empty())
    //{
    //  Trace(c) << "INST-EXPLAIN: LOCAL RESOLUTION COMPRESSION" << std::endl;
    //}
  }
  // clean up the path
  genPath.erase(lit);
  return true;
}

bool InstExplainPfGen::instExplainFind(IexOutput& iout,
                                       IexProof& g,
                                       Node opl,
                                       Node pl,
                                       Node inst,
                                       std::map<Node, bool>& genPath,
                                       bool reqPureGen,
                                       const char* c,
                                       unsigned tb)
{
  std::map<Node, InstExplainLit>::iterator itl;
  if (!d_ied.findInstExplainLit(pl, itl))
  {
    // no instantiation information for ground literal, we fail
    g.setOpenConclusion(iout, opl, opl);
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
    g.setOpenConclusion(iout, opl, opl);
    return false;
  }
  Assert(!opl.isNull());
  // populate choices for the proof regression, which we store in
  // g.d_conclusions[opl]
  std::map<Node, IexProof>& pconcs = g.d_conclusions[opl];
  Assert(pconcs.empty());
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
  unsigned rstart = (opl.isNull() && !reqPureGen) ? 1 : 0;
  unsigned rend = reqPureGen ? 1 : 2;
  for (unsigned r = rstart; r < rend; r++)
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
      bool doRec = true;
      if (!opl.isNull())
      {
        doRec = g.checkCompatible(r == 0 ? opl : opli, r == 0 ? opli : opl);
      }
      if (doRec)
      {
        Trace(c) << "  ...compatible, recurse, phase="
                 << (r == 0 ? "assume" : "conclude") << std::endl;
        // recurse now
        Assert(opl.isNull() || pconcs.find(opli) == pconcs.end());
        bool undoOpli = true;
        if (instExplain(iout,
                        pconcs[opli],
                        opli,
                        pl,
                        instpl,
                        genPath,
                        reqPureGen || r == 0,
                        c,
                        tb + 3))
        {
          if (opl.isNull())
          {
            // Don't have criteria to judge what is best, due to incomparable
            // matching.
            // TODO: could do subsumption to prune here
            undoOpli = false;
          }
          else if (pconcs[opli].isPurelyGeneral())
          {
            // if it is purely general, we are done if r==0, otherwise,
            // we mistakenly found a purely general proof of something where
            // we needed an open conclusion.
            best = opli;
            if (r == 0)
            {
              break;
            }
            else
            {
              // should have already found this when r was 0
              Assert(!g.checkCompatible(opl, opli));
              // if we needed an open conclusion, we explicitly add "true"
              // as the open conclusion, which will become the UPG.
              Node t = NodeManager::currentNM()->mkConst(true);
              pconcs[opli].setOpenConclusion(iout, t, t);
              break;
            }
          }
          else
          {
            // if it wasn't purely general, we must not have required it to be
            Assert(r == 1);
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
        Trace(c) << "  ...incompatible, phase="
                 << (r == 0 ? "assume" : "conclude") << std::endl;
      }
    }
    // found one that met the criteria
    if (!best.isNull())
    {
      break;
    }
    // search for instantiations that would have propagated this
    /*
    Node f;
    Node g;
    bool pol;
    if( d_ied.getLitSymbolIndex(opl, f,g,pol) )
    {
      Trace(c) << "(has " << d_ied.d_plit_map[f][g][pol].size() << " possible propagating literals)" << std::endl;
    }
    else
    {
      Trace(c) << "...could not get symbol index for " << opl << std::endl;
    }
    */
  }
  // TODO: search for instantiations that would have propagated this??

  // now, take the best generalization if there are any available
  if (pconcs.empty())
  {
    // we no longer have a valid conclusion, remove it
    if (Trace.isOn(c))
    {
      indent(c, tb + 1);
      Trace(c) << "-> failed to generalize" << std::endl;
    }
    g.setOpenConclusion(iout, opl, opl);
    return false;
  }
  if (opl.isNull())
  {
    // we leave multiple possible conclusions here
    return true;
  }
  Assert(!best.isNull());
  Assert(pconcs.find(best) != pconcs.end());
  if (Trace.isOn(c))
  {
    indent(c, tb + 1);
    Trace(c) << "CHOOSE to set conclusion " << best << std::endl;
    indent(c, tb + 1);
  }
  // Set the conclusion to the one on child "best".
  // This will merge it into the parent if it has no open leaves.
  g.setConclusion(iout, opl, best);
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
