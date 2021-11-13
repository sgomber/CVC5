/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Info per quantified formula in CCFV.
 */

#include "theory/quantifiers/ccfv/quant_info.h"

#include "expr/node_algorithm.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
  
QuantInfo::QuantInfo(context::Context * c) : d_isActive(c), d_watchMatcherIndex(c)
{
}

void QuantInfo::initialize(TNode q, expr::TermCanonize& tc)
{
  Assert (q.getKind()==FORALL);
  d_quant = q;
  std::map<TNode, Node> visited;
  d_canonBody = tc.getCanonicalTerm(q[1], visited);
  std::map<TNode, Node>::iterator it;
  for (const Node& v : q[0])
  {
    it = visited.find(v);
    if (it!=visited.end())
    {
      d_canonVars.push_back(it->second);
    }
    else
    {
      Assert (false);
      d_canonVars.push_back(v);
    }
  }
  // now compute matching requirements
  computeMatchingRequirements();
}

void QuantInfo::computeMatchingRequirements()
{
  std::unordered_set<std::pair<TNode, int32_t>> visited;
  std::unordered_set<std::pair<TNode, int32_t>>::iterator it;
  std::vector<std::pair<TNode, int32_t>> visit;
  std::pair<TNode, int32_t> cur;
  visit.push_back(std::pair<TNode, int32_t>(n, -1));
  do {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end()) {
      visited.insert(cur);
      // is it a Boolean connective?
      Assert (cur.first.getType().isBoolean());
      Kind k = cur.first.getKind();
      if (expr::isBooleanConnective(cur.first))
      {
        int32_t childIndex;
        switch (k)
        {
          case SEP_STAR:
          case AND:
          case OR:
            childIndex = (pol==(k==OR)) ? 0 : cur.second;
            break;
          case NOT:
            childIndex = -cur.second;
            break;
          case ITE:
          case EQUAL:
            childIndex = 0;
            break;
          default:
            Unhandled() << "Unhandled Boolean connective " << k;
            break;
        }
        for (TNode tc : cur.first)
        {
          visit.push_back(std::pair<TNode, int32_t>(tc, childIndex));
        }
      }
      else
      {
        bool pol = cur.second>=0;
        bool hasPol = cur.second!=0;
        addMatchRequirement(cur.first, pol, hasPol);
      }
    }
  } while (!visit.empty());
}

void QuantInfo::addMatchRequirement(TNode lit, bool pol, bool hasPol)
{
  Assert (lit.getType().isBoolean());
  Kind k = lit.getKind();
  if (k==FORALL)
  {
    // do nothing, unhandled
  }
  else if (k==EQUAL)
  {
    // maybe ground
    for (size_t i=0; i<2; i++)
    {
      if (!expr::hasFreeVar(lit[i]))
      {
        
      }
    }
  }
  else if (inst::TriggerTermInfo::isAtomicTriggerKind(k))
  {
    // matchable predicate
  }
  else
  {
    // unmatchable predicate, add all of its children without polarity, for
    // each that contain free variables
    for (TNode lc : lit)
    {
      addMatchTerm(lc);
    }
  }
}

void QuantInfo::addMatchTermReq(TNode t, Node eqc, bool isEq)
{
  std::vector<Node>& reqs = isEq ? d_matcherEqReq[t] : d_matcherDeqReq[t];
  if (std::find(reqs.begin(), reqs.end(), eqc)==reqs.end())
  {
    reqs.push_back(eqc);
  }
}

void QuantInfo::addMatchTerm(TNode t)
{
  // to be propagating, it must be disequal from nothing
  addMatchTermReq(t, Node::null(), false);
}

void QuantInfo::resetRound()
{
  // TODO: compute order of matchers in d_matchers?
}

TNode QuantInfo::getNextMatcher()
{
  if (!d_isActive.get())
  {
    return TNode::null();
  }
  // TODO: when to increment watch matcher?
  Assert (d_watchMatcherIndex.get()<d_matchers.size());

  return d_matchers[d_watchMatcherIndex.get()];
}

const std::map<TNode, Node>& QuantInfo::getMatchConstraints(bool isEq) const
{
  return isEq ? d_matcherEqReq : d_matcherDeqReq;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

