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

QuantInfo::QuantInfo(context::Context* c) : d_isActive(c) {}

void QuantInfo::initialize(TNode q,
                           eq::EqualityEngine* ee,
                           expr::TermCanonize& tc)
{
  Assert(q.getKind() == FORALL);
  d_quant = q;

  // canonize the body of the quantified formula
  std::map<TNode, Node> visited;
  d_canonBody = tc.getCanonicalTerm(q[1], visited);

  // compute the variable correspondence
  std::map<TNode, Node>::iterator it;
  std::vector<std::pair<size_t, TNode>> varList;
  std::vector<TNode> uncontainedVar;
  for (const Node& v : q[0])
  {
    it = visited.find(v);
    if (it != visited.end())
    {
      TNode cv = it->second;
      d_canonVars.push_back(cv);
      size_t index = tc.getIndexForFreeVariable(cv);
      varList.push_back(std::pair<size_t, TNode>(index, cv));
    }
    else
    {
      Assert(false);
      d_canonVars.push_back(v);
      uncontainedVar.push_back(v);
    }
  }
  // Sort variables by their index in the term canonizer. This is to ensure
  // a variable ordering in the driver where shared variables are assigned
  // first.
  std::sort(varList.begin(), varList.end());
  for (std::pair<size_t, TNode>& vl : varList)
  {
    d_canonVarOrdered.push_back(vl.second);
  }
  d_canonVarOrdered.insert(
      d_canonVarOrdered.end(), uncontainedVar.begin(), uncontainedVar.end());
  Assert(d_canonVarOrdered.size() == q[0].getNumChildren());

  // compute matching requirements
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
      computeMatchReq(cur, ee, visit);
    }
  } while (!visit.empty());

  // now we go back and process terms in the match requirements
  processMatchReqTerms(ee);
  
  // TODO: debug print
}

void QuantInfo::computeMatchReq(TNode cur,
                                eq::EqualityEngine* ee,
                                std::vector<TNode>& visit)
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
    // double negations should already be eliminated
    Assert(k != NOT);
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
  if (k == EQUAL || ee->isFunctionKind(k) || expr::isBooleanConnective(cur))
  {
    // Equality between patterns, matchable predicate, or Boolean connective.
    // Note that equalities and Boolean connectives are simply marked as
    // constraints here, the main algorithm will determine how to process them.
    // Flip polarity since we want to falsify.
    Node eqc = NodeManager::currentNM()->mkConst(!pol);
    addMatchTermReq(cur, eqc, true);
    return;
  }
  // Unmatchable predicate, add all of its children without polarity.
  for (TNode lc : cur)
  {
    // to be propagating, it must be equal to something
    addMatchTermReq(lc, Node::null(), true);
  }
}

void QuantInfo::addMatchTermReq(TNode t, Node eqc, bool isEq)
{
  // if we have no free variables
  if (!expr::hasFreeVar(t))
  {
    if (!eqc.isNull())
    {
      // this should only happen if miniscoping
    }
    return;
  }
  // if not equal, make (not (= t eqc))
  if (!isEq)
  {
    Assert(!eqc.isNull());
    eqc = t.eqNode(eqc).notNode();
  }
  std::vector<Node>& reqs = d_req[t];
  if (std::find(reqs.begin(), reqs.end(), eqc) == reqs.end())
  {
    reqs.push_back(eqc);
  }
}

void QuantInfo::processMatchReqTerms(eq::EqualityEngine* ee)
{
  // Now, traverse each of the terms in match requirements. This sets up:
  // (1) d_congTerms, the set of terms we are doing congruence over
  // (2) d_topLevelMatchers, the set of terms that we may do matching with,
  // which is the set of terms in the body of ee that do not occur beneath
  // a congruence term.
  // (3) d_unknownTerms, the set of subterms we don't know how to handle.
  // (4) d_termMaxVar, which maps congruence terms to the variable they
  // watch to be fully defined.

  // We track pairs (t, b) where t is the term we are traversing, and b is
  // whether we have traversed inside a congruence term.
  std::unordered_map<std::pair<TNode, bool>, bool, NodeBoolPairHashFunction>
      visited;
  std::unordered_map<std::pair<TNode, bool>, bool, NodeBoolPairHashFunction>::
      iterator it;
  std::vector<std::pair<TNode, bool>> visit;
  std::pair<TNode, bool> cur;
  // set d_reqTerms and add them all for traversal
  for (const std::pair<const TNode, std::vector<Node>>& r : d_req)
  {
    d_reqTerms.push_back(r.first);
    visit.push_back(std::pair<TNode, bool>(r.first, false));
  }
  // track parents list
  std::map<TNode, std::vector<TNode>> parentList;
  std::unordered_set<TNode> topLevelMatchers;
  // traverse
  while (!visit.empty())
  {
    cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      // don't care about terms without free variables
      if (!expr::hasFreeVar(cur.first))
      {
        visit.pop_back();
        visited[cur] = true;
        continue;
      }
      Kind k = cur.first.getKind();
      bool inCongTerm = cur.second;
      // if we are a variable, or do congruence over this kind
      if (k == BOUND_VARIABLE || ee->isFunctionKind(k))
      {
        if (!inCongTerm)
        {
          // record top level matcher
          topLevelMatchers.insert(cur.first);
          // we are now within a congruence term
          visit.pop_back();
          visited[cur] = true;
          // Mark to visit self as non-top level. This ensures we only add each
          // term to d_congTerms once.
          visit.push_back(std::pair<TNode, bool>(cur.first, true));
          continue;
        }
        else
        {
          // will add to congruence terms at post-traversal
          visited[cur] = false;
        }
      }
      else if (!inCongTerm && expr::isBooleanConnective(cur.first))
      {
        // if we are not in a congruence term, and we are Boolean connective,
        // recurse
        visit.pop_back();
        visited[cur] = true;
      }
      else
      {
        // not handled as Boolean connective or congruence kind, do nothing
        // we remember the term as an unknown term.
        d_unknownTerms.insert(cur.first);
        visit.pop_back();
        visited[cur] = true;
        continue;
      }
      // recurse to children
      if (cur.first.getNumChildren() > 0)
      {
        for (TNode cc : cur.first)
        {
          visit.push_back(std::pair<TNode, bool>(cc, inCongTerm));
          // remember the parent list
          parentList[cc].push_back(cur.first);
        }
      }
    }
    else
    {
      visit.pop_back();
      if (!it->second)
      {
        visited[cur] = true;
        // we will add this term to the equality engine. We add at post-order
        // traversal to that the order of terms is correct, i.e. we add subterms
        // first.
        d_congTerms.push_back(cur.first);
      }
    }
  }
  std::unordered_set<TNode>::iterator itc;
  std::map<TNode, std::vector<TNode>>::iterator itpl;
  std::map<TNode, std::vector<Node>>::iterator itr;
  std::unordered_set<TNode> usedMatchers;
  for (TNode v : d_canonVarOrdered)
  {
    // for each variable, we ensure that this variable occurs in the list
    // of top-level matchers d_topLevelMatchers so far. We add one term.
    Node tlMatcher;
    size_t tlMatcherScore = 0;
    bool alreadyMatcher = false;
    std::vector<TNode> ctnVisit;
    std::unordered_set<TNode> containing;
    TNode ccur;
    ctnVisit.push_back(v);
    do
    {
      ccur = ctnVisit.back();
      ctnVisit.pop_back();
      itc = containing.find(ccur);
      if (itc == containing.end())
      {
        containing.insert(ccur);
        if (!alreadyMatcher)
        {
          // if this is a top-level matcher
          itc = topLevelMatchers.find(ccur);
          if (itc != topLevelMatchers.end())
          {
            if (usedMatchers.find(ccur) != usedMatchers.end())
            {
              // It may already be added (e.g. to match an earlier variable).
              // In this case, we don't need to add a new matcher
              alreadyMatcher = true;
            }
            else if (tlMatcherScore < 3)
            {
              // prefer matchers in increasing order:
              // 0-no constraints, 1-null constraint, 2-disequality, 3-equality
              size_t tlCurScore = 0;
              itr = d_req.find(ccur);
              if (itr != d_req.end())
              {
                for (const Node& cs : itr->second)
                {
                  if (cs.isNull())
                  {
                    tlCurScore = 1;
                  }
                  else if (isDeqConstraint(cs, ccur))
                  {
                    tlCurScore = 2;
                  }
                  else
                  {
                    tlCurScore = 3;
                    break;
                  }
                }
              }
              if (tlMatcher.isNull() || tlCurScore > tlMatcherScore)
              {
                // Take this as the new best candidate matcher
                tlMatcher = ccur;
                tlMatcherScore = tlCurScore;
              }
            }
          }
        }
        // we have fvars[i] < fvars[j] for i < j, set or overwrite the max
        // variable here.
        d_termMaxVar[ccur] = v;
        itpl = parentList.find(ccur);
        if (itpl != parentList.end())
        {
          ctnVisit.insert(
              ctnVisit.end(), itpl->second.begin(), itpl->second.end());
        }
      }
    } while (!ctnVisit.empty());
    // if we don't already have a matcher for this variable
    if (!alreadyMatcher)
    {
      if (!tlMatcher.isNull())
      {
        // use the matcher for this variable
        d_matchers[v] = tlMatcher;
        // Notice that variables in d_canonVarOrdered are assigned in order,
        // thus this justifies matching for future variables.
        usedMatchers.insert(tlMatcher);
      }
      else
      {
        // Assert that no matchers exist?
      }
    }
  }
}

void QuantInfo::resetRound()
{
  d_isActive = true;
  d_initVarIndex = 0;
}

TNode QuantInfo::getNextSearchVariable()
{
  if (d_initVarIndex >= d_canonVarOrdered.size())
  {
    return TNode::null();
  }
  TNode next = d_canonVarOrdered[d_initVarIndex];
  d_initVarIndex++;
  return next;
}

TNode QuantInfo::getMatcherFor(TNode v) const
{
  std::map<TNode, TNode>::const_iterator it = d_matchers.find(v);
  if (it == d_matchers.end())
  {
    return TNode::null();
  }
  return it->second;
}

const std::vector<TNode>& QuantInfo::getFreeVariables() const
{
  return d_canonVars;
}

const std::vector<TNode>& QuantInfo::getOrderedFreeVariables() const
{
  return d_canonVarOrdered;
}

const std::map<TNode, std::vector<Node>>& QuantInfo::getConstraints() const
{
  return d_req;
}

const std::vector<TNode>& QuantInfo::getConstraintTerms() const
{
  return d_reqTerms;
}
const std::vector<TNode>& QuantInfo::getCongruenceTerms() const
{
  return d_congTerms;
}

const std::map<TNode, TNode>& QuantInfo::getTermMaxVarMap() const
{
  return d_termMaxVar;
}

bool QuantInfo::isActive() const { return d_isActive.get(); }

void QuantInfo::setActive(bool val) { d_isActive = val; }

bool QuantInfo::isDeqConstraint(TNode c, TNode p)
{
  return c.getKind() == NOT && c[0].getKind() == EQUAL && c[0][0] == p;
}
bool QuantInfo::isDeqConstraint(TNode p, TNode c, TNode& val)
{
  if (isDeqConstraint(c, p))
  {
    val = c[0][1];
    return true;
  }
  return false;
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
