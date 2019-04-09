/*********************                                                        */
/*! \file gen_lit_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Generalized literal info
 **/

#include "theory/quantifiers/gen_lit_info.h"

#include "theory/quantifiers/inst_explain_db.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void GLitInfo::initialize(InstExplainInst* iei)
{
  d_iei = iei;
  d_subs_modify.clear();
  d_assumptions.clear();
  d_conclusions.clear();
}

/*
bool GLitInfo::initialize(TNode a,
                          const GLitInfo& ga,
                          TNode b,
                          const GLitInfo& gb)
{
  // copy info from ga
  d_iei = ga.d_iei;
  d_subs_modify = ga.d_subs_modify;
  return merge(a, b, gb);
}

bool GLitInfo::merge(TNode a, TNode b, const GLitInfo& gb, bool allowBind)
{
  return mergeInternal(a, b, gb, true, allowBind);
}
*/

bool GLitInfo::setConclusion(Node pl, Node opl)
{
  std::map<Node, std::map<Node, GLitInfo>>::iterator it =
      d_conclusions.find(pl);
  if (it == d_conclusions.end())
  {
    return false;
  }
  std::map<Node, GLitInfo>::iterator it2 = it->second.find(opl);
  if (it2 == it->second.end())
  {
    return false;
  }
  // if child is purely general, we can compress and remove this
  if (it2->second.d_conclusions.empty())
  {
    // take its assumptions
    d_assumptions.insert(d_assumptions.end(),
                         it2->second.d_assumptions.begin(),
                         it2->second.d_assumptions.end());
    d_conclusions.erase(pl);
  }
  return true;
}

bool GLitInfo::checkCompatible(TNode a, TNode b, const GLitInfo& gb)
{
  return mergeInternal(a, b, gb, false, false);
}
bool GLitInfo::checkCompatible(TNode a, TNode b)
{
  GLitInfo gb;
  return mergeInternal(a, b, gb, false, false);
}

bool GLitInfo::mergeInternal(
    TNode a, TNode b, const GLitInfo& gb, bool doMerge, bool allowBind)
{
  // cannot carry conclusions currently
  if (doMerge && !gb.d_conclusions.empty())
  {
    return false;
  }
  // bound variables (in case we decide to cleanup)
  std::vector<TNode> bound_avars;
  Trace("ied-ginfo") << "GLitInfo::merge, a : " << a << std::endl;
  Trace("ied-ginfo") << "GLitInfo::merge, b : " << b << std::endl;
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
      Trace("ied-ginfo-debug") << "Match a:" << cura << std::endl;
      Trace("ied-ginfo-debug") << "Match b:" << curb << std::endl;
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
            Trace("ied-ginfo") << "GLitInfo::merge: Fail: induced equality on "
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
          Trace("ied-ginfo")
              << "GLitInfo::merge: bind " << cura << " -> " << bv << std::endl;
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
                Trace("ied-ginfo")
                    << "GLitInfo::merge: Fail: " << cura << " == " << curb
                    << ", where " << curb << " == " << x << std::endl;
                Trace("ied-ginfo")
                    << "GLitInfo::merge: which contradicts ( "
                    << d_subs_modify[x] << " == ) " << x << " == " << curb
                    << "( == " << bv << " ) " << std::endl;
                matchSuccess = false;
                break;
              }
              else
              {
                Trace("ied-ginfo") << "GLitInfo::merge: bind (backwards) " << x
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
              Trace("ied-ginfo")
                  << "GLitInfo::merge: Fail: clash ( " << av << " == ) " << cura
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
            Trace("ied-ginfo") << "GLitInfo::merge: Fail: operator ( " << av
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
  if (doMerge)
  {
    // carry the assumptions
    d_assumptions.insert(
        d_assumptions.end(), gb.d_assumptions.begin(), gb.d_assumptions.end());
  }
  Trace("ied-ginfo") << "GLitInfo::merge: Success!" << std::endl;
  return true;
}

bool GLitInfo::drop(TNode b)
{
  // drop free variables
  return true;
}

bool GLitInfo::isPurelyGeneral() const { return d_conclusions.empty(); }

Node GLitInfo::getAssumptions() const
{
  NodeManager* nm = NodeManager::currentNM();
  if (d_assumptions.empty())
  {
    return nm->mkConst(true);
  }
  return d_assumptions.size() == 1 ? d_assumptions[0]
                                   : nm->mkNode(AND, d_assumptions);
}

bool GLitInfo::isOpen(Node lit) const
{
  return d_conclusions.find(lit) != d_conclusions.end();
}

bool GLitInfo::hasUPG() const { return true; }

InstExplainInst* GLitInfo::getUPG(std::vector<Node>& concs,
                                  Node& quant,
                                  std::vector<Node>& assumptions) const
{
  InstExplainInst* ret = nullptr;
  // add assumptions here
  assumptions.insert(
      assumptions.end(), d_assumptions.begin(), d_assumptions.end());
  bool addedConc = false;
  for (const std::pair<Node, std::map<Node, GLitInfo>>& cs : d_conclusions)
  {
    for (const std::pair<Node, GLitInfo>& cc : cs.second)
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
void GLitInfo::processUPG(InstExplainDb& ied,
                          Node currConc,
                          std::vector<Node>& assumptions,
                          std::vector<Node>& lemmas,
                          std::map<Node, Node>& subsumptions) const
{
  std::vector<Node> concs;
  Node upgLit;
  const GLitInfo* gupg = nullptr;
  for (const std::pair<Node, std::map<Node, GLitInfo>>& cs : d_conclusions)
  {
    for (const std::pair<Node, GLitInfo>& cc : cs.second)
    {
      if (!cc.second.d_conclusions.empty())
      {
        gupg = &(cc.second);
        upgLit = cc.first;
      }
      // if we are open, then we must add to conclusions for this
      concs.push_back(cc.first.negate());
    }
  }
  assumptions.insert(
      assumptions.end(), d_assumptions.begin(), d_assumptions.end());
  // If at least one part of the proof is purely general, we infer a lemma
  // that subsumes this quantified formula.
  if (assumptions.size()>1)
  {
    if (!currConc.isNull())
    {
      // if we are carrying an open conclusion, add it now
      concs.push_back(currConc);
    }
    Assert( d_iei );
    Node genConc = ied.getGeneralizedConclusion(d_iei,assumptions,concs,lemmas);
    // add this quantified formula to assumptions if we are recursing
    if (gupg)
    {
      assumptions.push_back(genConc);
    }
  }
  if (gupg)
  {
    gupg->processUPG(ied, Node::null(), assumptions, lemmas, subsumptions);
  }
}

unsigned GLitInfo::getScore() const { return d_conclusions.size(); }

void GLitInfo::indent(const char* c, unsigned tb) const
{
  for (unsigned i = 0; i < tb; i++)
  {
    Trace(c) << " ";
  }
}
void GLitInfo::debugPrint(const char* c, unsigned tb) const
{
  if (Trace.isOn(c))
  {
    indent(c, tb);
    Trace(c) << "MATCH_INFO" << std::endl;
    indent(c, tb + 1);
    Trace(c) << "substitution:" << std::endl;
    if (d_subs_modify.empty())
    {
      indent(c, tb + 2);
      Trace(c) << "(empty)" << std::endl;
    }
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
      for (const std::pair<Node, std::map<Node, GLitInfo>>& cs : d_conclusions)
      {
        for (const std::pair<Node, GLitInfo>& cc : cs.second)
        {
          indent(c, tb + 2);
          Trace(c) << cs.first << " / " << cc.first << std::endl;
        }
      }
    }
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
