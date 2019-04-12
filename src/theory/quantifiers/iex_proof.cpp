/*********************                                                        */
/*! \file iex_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of instantiation explain proof class
 **/

#include "theory/quantifiers/iex_proof.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/inst_explain_db.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Node IexOutput::reportConclusion(InstExplainInst* iei,
                                 const std::vector<Node>& assumps,
                                 const std::vector<Node>& concs,
                                 bool doGenCInst)
{
  return d_iexd.getGeneralizedConclusion(
      iei, assumps, concs, d_lemmas, d_subsumed_by, doGenCInst);
}
bool IexOutput::empty() const
{
  return d_lemmas.empty() && d_subsumed_by.empty();
}

bool IexProof::empty() const
{
  return d_subs_modify.empty() && d_assumptions.empty()
         && d_conclusions.empty();
}
void IexProof::initialize(InstExplainInst* iei)
{
  d_iei = iei;
  d_subs_modify.clear();
  d_assumptions.clear();
  d_conclusions.clear();
}

void IexProof::setConclusion(IexOutput& iout, Node pl, Node opl)
{
  std::map<Node, std::map<Node, IexProof>>::iterator it =
      d_conclusions.find(pl);
  Assert(it != d_conclusions.end());
  // should have cleaned up all others if we are here
  Assert(it->second.size() == 1);
  std::map<Node, IexProof>::iterator it2 = it->second.find(opl);
  Assert(it2 != it->second.end());
  // if child is purely general, we can compress and remove this
  if (it2->second.isPurelyGeneral())
  {
    // we may be able to create a subsuming resolution here
    if (options::iexLocalCompress())
    {
      if (Trace.isOn("iex-proof-debug"))
      {
        Trace("iex-proof-debug") << "=== Process local proof:" << std::endl;
        it2->second.debugPrint("iex-proof-debug");
        Trace("iex-proof-debug") << "=== with " << opl << std::endl;
      }
      it2->second.processUPG(iout, opl);
      Trace("iex-proof-debug") << "=== END PROCESS " << std::endl;
    }
    // take its assumptions and remove it
    d_assumptions.insert(d_assumptions.end(),
                         it2->second.d_assumptions.begin(),
                         it2->second.d_assumptions.end());
    d_conclusions.erase(pl);
  }
  else
  {
    // it is an open conclusion, must register it as UPG if possible
    notifyOpenConclusion(iout, pl, opl, false);
  }
}
void IexProof::setOpenConclusion(IexOutput& iout, Node pl, Node opl)
{
  // it is an open conclusion, clear its proof
  setOpenConclusionInternal(iout, pl, opl);
  // must register it as UPG
  notifyOpenConclusion(iout, pl, opl, true);
}
void IexProof::setOpenConclusionInternal(IexOutput& iout, Node pl, Node opl)
{
  if (options::iexLocalCompress())
  {
    if (Trace.isOn("iex-proof-debug"))
    {
      Trace("iex-proof-debug")
          << "=== Process local proof (open):" << std::endl;
      d_conclusions[pl][opl].debugPrint("iex-proof-debug");
      Trace("iex-proof-debug") << "=== with " << opl << std::endl;
    }
    d_conclusions[pl][opl].processUPG(iout, opl);
    Trace("iex-proof-debug") << "=== END PROCESS " << std::endl;
  }
  d_conclusions.erase(pl);
  d_conclusions[pl][opl].initialize(nullptr);
}

void IexProof::notifyOpenConclusion(IexOutput& iout,
                                    Node pl,
                                    Node opl,
                                    bool isTriv)
{
  std::vector<Node> lemmas;
  Assert(!opl.isNull());
  // if we had a non-trivial UPG
  if (!d_upgTriv)
  {
    Assert(!d_upgLit.isNull());
    //
    // d_conclusions[d_upgLit][d_upgOLit].processUPG(d_upgOLit);
    // clear the previous non-trivial UPG
    setOpenConclusionInternal(iout, d_upgLit, d_upgOLit);
    // it is now trivial
    d_upgTriv = true;
  }
  // if the upg literal is available, set it.
  if (d_upgLit.isNull())
  {
    d_upgLit = pl;
    d_upgOLit = opl;
    d_upgTriv = isTriv;
  }
  else if (!isTriv)
  {
    //
    // d_conclusions[d_upgLit][d_upgOLit].processUPG(d_upgOLit);
    // otherwise, have to clear the current one if its non-trivial
    setOpenConclusionInternal(iout, pl, opl);
  }
}

bool IexProof::checkCompatible(TNode a, TNode b, const IexProof& gb)
{
  return mergeInternal(a, b, gb, false);
}
bool IexProof::checkCompatible(TNode a, TNode b)
{
  IexProof gb;
  return mergeInternal(a, b, gb, false);
}

bool IexProof::mergeInternal(TNode a,
                             TNode b,
                             const IexProof& gb,
                             bool allowBind)
{
  // bound variables (in case we decide to cleanup)
  std::vector<TNode> bound_avars;
  Trace("iex-pf") << "IexProof::merge, a : " << a << std::endl;
  Trace("iex-pf") << "IexProof::merge, b : " << b << std::endl;
  // the visit cache and indicates unifier information
  std::map<Node, std::unordered_set<Node, NodeHashFunction>> visited;
  std::vector<Node> avisit;
  std::vector<Node> bvisit;
  std::map<TNode, Node>::const_iterator it;
  std::map<Node, std::unordered_set<Node, NodeHashFunction>>::iterator itv;
  avisit.push_back(a);
  bvisit.push_back(b);
  TNode cura;
  TNode curb;
  bool matchSuccess = true;
  do
  {
    cura = avisit.back();
    avisit.pop_back();
    curb = bvisit.back();
    bvisit.pop_back();
    std::unordered_set<Node, NodeHashFunction>& va = visited[cura];
    if (va.find(curb) == va.end())
    {
      va.insert(curb);
      Trace("iex-pf-debug") << "Match a:" << cura << std::endl;
      Trace("iex-pf-debug") << "Match b:" << curb << std::endl;
      bool abv = cura.getKind() == BOUND_VARIABLE;
      bool bbv = curb.getKind() == BOUND_VARIABLE;
      // TODO: check that it is bound by the quantified formula

      TNode av = cura;
      if (abv)
      {
        it = d_subs_modify.find(cura);
        if (it != d_subs_modify.end())
        {
          av = it->second;
          abv = false;
        }
      }
      TNode bv = curb;
      if (bbv)
      {
        it = gb.d_subs_modify.find(curb);
        if (it != gb.d_subs_modify.end())
        {
          bv = it->second;
          bbv = false;
        }
      }
      if (abv)
      {
        // two variables
        if (bbv)
        {
          // store reversed to ensure that we bind cura if curb becomes bound
          // later
          visited[curb].insert(cura);
          if (visited[curb].size() > 1)
          {
            Trace("iex-pf") << "IexProof::merge: Fail: induced equality on "
                            << curb << std::endl;
            matchSuccess = false;
            break;
          }
        }
        else if (allowBind)
        {
          // An a-variable is bound, simple.
          // FIXME:
          // P(x) { x -> f(b) } matching P(f(y)) { y -> b }, drop to x -> f(b)
          Trace("iex-pf") << "IexProof::merge: bind " << cura << " -> " << bv
                          << std::endl;
          d_subs_modify[cura] = bv;
          bound_avars.push_back(cura);
        }
        else
        {
          return false;
        }
      }
      else
      {
        if (bbv)
        {
          // A b-variable was bound.
          // must go back and bind all occurrences it was equal to
          itv = visited.find(curb);
          if (itv != visited.end())
          {
            if (!allowBind)
            {
              return false;
            }
            for (TNode x : itv->second)
            {
              if (x != av && x.getKind() != BOUND_VARIABLE)
              {
                // b-variable bound to two non-variable terms
                return false;
              }
              if (d_subs_modify.find(x) != d_subs_modify.end())
              {
                // bound to different things, fail?
                Trace("iex-pf")
                    << "IexProof::merge: Fail: " << cura << " == " << curb
                    << ", where " << curb << " == " << x << std::endl;
                Trace("iex-pf")
                    << "IexProof::merge: which contradicts ( "
                    << d_subs_modify[x] << " == ) " << x << " == " << curb
                    << "( == " << bv << " ) " << std::endl;
                matchSuccess = false;
                break;
              }
              else
              {
                Trace("iex-pf") << "IexProof::merge: bind (backwards) " << x
                                << " -> " << av << std::endl;
                d_subs_modify[x] = av;
              }
            }
            if (!matchSuccess)
            {
              break;
            }
          }
          else
          {
            visited[curb].insert(av);
          }
        }
        else if (av != bv)
        {
          // recurse
          if (av.hasOperator())
          {
            if (!bv.hasOperator() || bv.getOperator() != av.getOperator()
                || bv.getNumChildren() != av.getNumChildren())
            {
              Trace("iex-pf")
                  << "IexProof::merge: Fail: clash ( " << av << " == ) " << cura
                  << " == " << curb << "( == " << bv << " ) " << std::endl;
              // wrong operators, should only happen if we within a substitution
              Assert(cura.getKind() == BOUND_VARIABLE
                     || curb.getKind() == BOUND_VARIABLE);
              matchSuccess = false;
              break;
            }
            for (unsigned i = 0, nchild = cura.getNumChildren(); i < nchild;
                 i++)
            {
              if (cura[i] != curb[i])
              {
                avisit.push_back(cura[i]);
                bvisit.push_back(curb[i]);
              }
            }
          }
          else
          {
            Trace("iex-pf") << "IexProof::merge: Fail: operator ( " << av
                            << " == ) " << cura << " == " << curb
                            << "( == " << bv << " ) " << std::endl;
            // not equal and a is a variable, fail
            return false;
          }
        }
      }
    }
  } while (!avisit.empty());

  if (!matchSuccess)
  {
    // revert the bound variables
    for (TNode avb : bound_avars)
    {
      Assert(d_subs_modify.find(avb) != d_subs_modify.end());
      d_subs_modify.erase(avb);
    }
    return false;
  }
  Trace("iex-pf") << "IexProof::merge: Success!" << std::endl;
  return true;
}

bool IexProof::drop(TNode b)
{
  // drop free variables
  return true;
}

bool IexProof::isPurelyGeneral() const { return d_conclusions.empty(); }

Node IexProof::getAssumptions() const
{
  NodeManager* nm = NodeManager::currentNM();
  if (d_assumptions.empty())
  {
    return nm->mkConst(true);
  }
  return d_assumptions.size() == 1 ? d_assumptions[0]
                                   : nm->mkNode(AND, d_assumptions);
}

bool IexProof::isOpen(Node lit) const
{
  return d_conclusions.find(lit) != d_conclusions.end();
}

bool IexProof::hasUPG() const { return true; }

InstExplainInst* IexProof::getUPG(std::vector<Node>& concs,
                                  Node& quant,
                                  std::vector<Node>& assumptions) const
{
  InstExplainInst* ret = nullptr;
  // add assumptions here
  assumptions.insert(
      assumptions.end(), d_assumptions.begin(), d_assumptions.end());
  bool addedConc = false;
  for (const std::pair<Node, std::map<Node, IexProof>>& cs : d_conclusions)
  {
    for (const std::pair<Node, IexProof>& cc : cs.second)
    {
      // are we a leaf? if so, we must add to conclusions
      if (cc.second.d_conclusions.empty())
      {
        Assert(!ret);
        // note the negation here
        concs.push_back(cc.first.negate());
        addedConc = true;
      }
      else
      {
        Assert(!ret);
        Assert(!addedConc);
        // recurse
        ret = cc.second.getUPG(concs, quant, assumptions);
      }
    }
  }
  if (addedConc)
  {
    Assert(d_iei);
    ret = d_iei;
    Node qg = ret->getQuantifiedFormula();
    Assert(quant.isNull() || quant == qg);
    quant = qg;
  }
  return ret;
}
void IexProof::processUPG(IexOutput& iout, Node currConc)
{
  // start with no assumptions
  std::vector<Node> assumptions;
  Node upgConc = processUPGInternal(iout, currConc, assumptions);
  if (!upgConc.isNull())
  {
    // compress assumptions
    d_assumptions.clear();
    d_conclusions.clear();
    d_assumptions.push_back(upgConc);
  }
}

Node IexProof::processUPGInternal(IexOutput& iout,
                                  Node currConc,
                                  std::vector<Node>& assumptions) const
{
  Trace("ied-process-upg") << "Process UPG, #assumps=" << assumptions.size()
                           << std::endl;
  // take assumptions from sibling proofs now
  assumptions.insert(
      assumptions.end(), d_assumptions.begin(), d_assumptions.end());
  std::vector<Node> concs;
  bool recUPG = false;
  Node ret;
  for (const std::pair<Node, std::map<Node, IexProof>>& cs : d_conclusions)
  {
    for (const std::pair<Node, IexProof>& cc : cs.second)
    {
      // if the proof is not a leaf
      if (!cc.second.d_conclusions.empty())
      {
        // should have only one UPG
        Assert(concs.empty());
        AlwaysAssert(!recUPG);
        recUPG = true;
        // cut the proof if applicable
        if (options::iexUPGCompress())
        {
          // we have a subsumption of the current quantified formula if there
          // is a sibling we generalized.
          if (assumptions.size() > 1)
          {
            Assert(d_iei);
            if (!currConc.isNull())
            {
              concs.push_back(currConc);
            }
            Assert(!cc.first.isNull());
            concs.push_back(cc.first.negate());
            // we do not do the generalized conflict instance in this call
            // we prefer generalized conflicting instances from the UPG.
            Node genConc = iout.reportConclusion(
                cc.second.d_iei, assumptions, concs, options::iexGenCInst());
            // we close the open conclusion
            assumptions.clear();
            // we become a premise only if we are not carrying a conclusion
            if (currConc.isNull())
            {
              assumptions.push_back(genConc);
            }
          }
        }
        // If we have an open conclusion, then the node we recurse on
        // is the new open conclusion. It is not negated since its polarity
        // is already flipped via the fact it is a conclusion.
        if (!currConc.isNull())
        {
          currConc = cc.first;
        }
        Trace("ied-process-upg") << "...follow " << cc.first << std::endl;
        ret = cc.second.processUPGInternal(iout, currConc, assumptions);
      }
      else
      {
        Assert(!cc.first.isNull());
        // if we are open, then we must add to conclusions for this
        concs.push_back(cc.first.negate());
      }
    }
  }
  // non-trivial proofs must have >1 assumptions.
  if (!recUPG && assumptions.size() > 1)
  {
    // must add the current conclusion if it exists
    if (!currConc.isNull())
    {
      concs.push_back(currConc);
    }
    // conclude the UPG
    return iout.reportConclusion(
        d_iei, assumptions, concs, options::iexGenCInst());
  }
  return ret;
}

unsigned IexProof::getScore() const { return d_conclusions.size(); }

void IexProof::indent(const char* c, unsigned tb) const
{
  for (unsigned i = 0; i < tb; i++)
  {
    Trace(c) << " ";
  }
}
void IexProof::debugPrint(const char* c, unsigned tb, bool rec) const
{
  if (Trace.isOn(c))
  {
    indent(c, tb);
    Trace(c) << "IEX" << std::endl;
    /*
    indent(c, tb + 1);
    Trace(c) << "substitution:" << std::endl;
    if (d_subs_modify.empty())
    {
      indent(c, tb + 2);
      Trace(c) << "(empty)" << std::endl;
    }
    */
    indent(c, tb + 1);
    Trace(c) << "assumptions:" << std::endl;
    if (d_assumptions.empty())
    {
      indent(c, tb + 2);
      Trace(c) << "(empty)" << std::endl;
    }
    else
    {
      for (const Node& a : d_assumptions)
      {
        indent(c, tb + 2);
        Trace(c) << a << std::endl;
      }
    }
    indent(c, tb + 1);
    Trace(c) << "conclusions:" << std::endl;
    if (d_conclusions.empty())
    {
      indent(c, tb + 2);
      Trace(c) << "(empty)" << std::endl;
    }
    else
    {
      for (const std::pair<Node, std::map<Node, IexProof>>& cs : d_conclusions)
      {
        for (const std::pair<Node, IexProof>& cc : cs.second)
        {
          indent(c, tb + 2);
          Trace(c) << cs.first << " / " << cc.first;
          if (rec)
          {
            Trace(c) << ":" << std::endl;
            cc.second.debugPrint(c, tb + 4, rec);
          }
          else
          {
            Trace(c) << std::endl;
          }
        }
      }
    }
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
