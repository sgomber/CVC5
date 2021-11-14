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
#include "expr/term_canonize.h"
#include "theory/quantifiers/ematching/trigger_term_info.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

QuantInfo::QuantInfo(context::Context* c)
    : d_isActive(c), d_watchMatcherIndex(c)
{
}

void QuantInfo::initialize(TNode q, expr::TermCanonize& tc)
{
  Assert(q.getKind() == FORALL);
  d_quant = q;

  // canonize the body of the quantified formula
  std::map<TNode, Node> visited;
  d_canonBody = tc.getCanonicalTerm(q[1], visited);

  // compute the variable correspondence
  std::map<TNode, Node>::iterator it;
  for (const Node& v : q[0])
  {
    it = visited.find(v);
    if (it != visited.end())
    {
      d_canonVars.push_back(it->second);
    }
    else
    {
      Assert(false);
      d_canonVars.push_back(v);
    }
  }

  // now compute matching requirements
  std::unordered_set<TNode> processed;
  std::unordered_set<TNode>::iterator itp;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(d_canonBody);
  do
  {
    cur = visit.back();
    visit.pop_back();
    itp = processed.find(cur);
    if (itp == processed.end())
    {
      processed.insert(cur);
      // process the match requirement for (disjunct) cur
      processMatchRequirement(cur, visit);
    }
  } while (!visit.empty());
}

void QuantInfo::processMatchRequirement(TNode cur, std::vector<TNode>& visit)
{
  Assert(cur.getType().isBoolean());
  bool pol = true;
  Kind k = cur.getKind();
  Assert(k != IMPLIES);
  if (k == OR)
  {
    // decompose OR
    visit.insert(visit.end(), cur.begin(), cur.end());
    return;
  }
  else if (k == NOT)
  {
    pol = false;
    cur = cur[0];
    k = cur.getKind();
    Assert(k != NOT);
  }
  if (k == FORALL)
  {
    // do nothing, unhandled
    return;
  }
  // NOTE: could sanitize the term, remove any nested quantifiers here?
  // This is probably not necessary, the equality engine will treat the term
  // as a leaf.
  if (k == EQUAL)
  {
    // maybe pattern equals ground?
    for (size_t i = 0; i < 2; i++)
    {
      if (!expr::hasFreeVar(cur[i]))
      {
        // Equality involving a ground term.
        // Flip polarity since we want to falsify.
        addMatchTermReq(cur[1 - i], cur[i], !pol);
        return;
      }
    }
  }
  else if (inst::TriggerTermInfo::isAtomicTriggerKind(k)
           || expr::isBooleanConnective(cur))
  {
    // Matchable predicate, or Boolean connective.
    // Note that Boolean connectives are simply marked as matching constraints
    // here, the main algorithm will determine how to process them.
    // Flip polarity since we want to falsify.
    Node eqc = NodeManager::currentNM()->mkConst(!pol);
    addMatchTermReq(cur, eqc, true);
    return;
  }
  // Unmatchable predicate, or equality between patterns.
  // Add all of its children without polarity.
  for (TNode lc : cur)
  {
    addMatchTerm(lc);
  }
}

void QuantInfo::addMatchTermReq(TNode t, Node eqc, bool isEq)
{
  if (!isEq)
  {
    Assert (!eqc.isNull());
    eqc = t.eqNode(eqc).notNode();
  }
  std::vector<Node>& reqs = d_matcherReq[t];
  if (std::find(reqs.begin(), reqs.end(), eqc) == reqs.end())
  {
    reqs.push_back(eqc);
  }
  if (std::find(d_matchers.begin(), d_matchers.end(), t) == d_matchers.end())
  {
    d_matchers.push_back(t);
  }
}

void QuantInfo::addMatchTerm(TNode t)
{
  // to be propagating, it must be disequal from nothing
  addMatchTermReq(t, Node::null(), true);
}

void QuantInfo::resetRound()
{
  // TODO: compute order of matchers in d_matchers heuristically?
  d_isActive = true;
  d_watchMatcherIndex = 0;
  Assert(!d_matchers.empty());
}

TNode QuantInfo::getNextMatcher()
{
  if (!d_isActive.get())
  {
    return TNode::null();
  }
  Assert(d_watchMatcherIndex.get() < d_matchers.size());
  TNode next = d_matchers[d_watchMatcherIndex.get()];
  d_watchMatcherIndex = d_watchMatcherIndex.get() + 1;
  return next;
}

const std::map<TNode, std::vector<Node>>& QuantInfo::getMatchConstraints() const
{
  return d_matcherReq;
}

const std::vector<TNode>& QuantInfo::getMatchers() const { return d_matchers; }

void QuantInfo::addCongruenceTerm(TNode t) { d_congTerms.push_back(t); }
const std::vector<TNode>& QuantInfo::getCongruenceTerms() const
{
  return d_congTerms;
}

bool QuantInfo::isActive() const { return d_isActive.get(); }

void QuantInfo::setActive(bool val) { d_isActive = val; }

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
