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
 * Congruence closure with free variables
 */

#include "theory/quantifiers/ccfv/inst_driver.h"

#include "theory/quantifiers/quantifiers_state.h"
#include "theory/uf/equality_engine.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

InstDriver::InstDriver(Env& env,
                       State& state,
                       QuantifiersState& qs,
                       TermRegistry& tr)
    : EnvObj(env), d_state(state), d_qstate(qs), d_treg(tr)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

void InstDriver::check(const std::vector<TNode>& quants)
{
  // reset round for all quantified formulas
  for (TNode q : quants)
  {
    QuantInfo& qi = d_state.getQuantInfo(q);
    qi.resetRound();
  }
  // reset search levels
  // NOTE: could incrementally maintain this?
  resetSearchLevels(quants);
}

void InstDriver::resetSearchLevels(const std::vector<TNode>& quants)
{
  // compute the levels at which the variables are at
  d_levels.clear();
  std::map<TNode, std::vector<TNode>> partition;
  std::map<TNode, size_t> fvLevel;
  assignVariableLevels(0, quants, partition, fvLevel);

  // set the start levels
  std::map<TNode, size_t>::iterator itf;
  for (TNode q : quants)
  {
    QuantInfo& qi = d_state.getQuantInfo(q);
    const std::vector<TNode>& fvs = qi.getOrderedFreeVariables();
    Assert(!fvs.empty());
    itf = fvLevel.find(fvs[0]);
    Assert(itf != fvLevel.end());
    SearchLevel& slevel = getSearchLevel(itf->second);
    slevel.d_startQuants.push_back(q);
  }
}

void InstDriver::assignVariableLevels(
    size_t level,
    const std::vector<TNode>& quants,
    std::map<TNode, std::vector<TNode>>& partition,
    std::map<TNode, size_t>& fvLevel)
{
  Assert(!quants.empty());
  // partition the quantifiers by their first variable
  SearchLevel& slevel = getSearchLevel(level);
  // every next variable must be included in this subtree
  std::vector<TNode> nextVars;
  // for each quantified formula that we require assigning next variable
  for (TNode q : quants)
  {
    QuantInfo& qi = d_state.getQuantInfo(q);
    TNode next = qi.getNextSearchVariable();
    if (next.isNull())
    {
      // fully assigned at this level
      slevel.d_finalQuants.push_back(q);
    }
    else
    {
      if (std::find(nextVars.begin(), nextVars.end(), next) == nextVars.end())
      {
        nextVars.push_back(next);
      }
      // add to the partition, which notice may be mixed with prior formulas
      // in the range of partition
      partition[next].push_back(q);
    }
  }
  // Add each variable to the search, which may make recursive calls that
  // process the variables lower. Those that are not processed in lower levels
  // are processed here.
  std::map<TNode, std::vector<TNode>>::iterator it;
  std::map<TNode, size_t>::iterator itl;
  for (TNode v : nextVars)
  {
    it = partition.find(v);
    if (it == partition.end())
    {
      // already processed at a lower level
      Assert(fvLevel.find(v) != fvLevel.end());
      continue;
    }
    // copy and remove from partition
    std::vector<TNode> nextQuants = it->second;
    partition.erase(it);
    // get next level
    size_t nextLevel;
    itl = fvLevel.find(v);
    if (itl != fvLevel.end())
    {
      // it might have been processed in another subtree that we were not
      // a part of
      nextLevel = itl->second + 1;
    }
    else
    {
      slevel.d_varsToAssign.push_back(v);
      fvLevel[v] = level;
      nextLevel = level + 1;
    }
    assignVariableLevels(nextLevel, nextQuants, partition, fvLevel);
  }
}

bool InstDriver::assignSearchLevel(size_t level)
{
  SearchLevel& slevel = getSearchLevel(level);
  Assert(!slevel.d_varsToAssign.empty());
  // find the next assignment for each variable
  std::vector<TNode> assignment;
  bool success = false;
  for (TNode v : slevel.d_varsToAssign)
  {
    PatTermInfo& pi = d_state.getPatTermInfo(v);
    const FreeVarInfo& fi = d_state.getFreeVarInfo(v);
    TNode eqc = pi.getNextWatchEqc();
    size_t qindex = 0;
    while (eqc.isNull() && qindex < fi.d_quantList.size())
    {
      // get the next quantified formula containing v
      TNode q = fi.d_quantList[qindex];
      qindex++;
      QuantInfo& qi = d_state.getQuantInfo(q);
      if (!qi.isActive())
      {
        // quantified formula is not active
        continue;
      }
      TNode matcher = qi.getCurrentMatcher();
      if (matcher.isNull())
      {
        // doesn't have a matcher, continue
        continue;
      }
      if (!processMatcher(qi, matcher))
      {
        // failed to process matcher, e.g. a top-level constraint was
        // not satisfied
        continue;
      }
      // maybe succeeded match?
      eqc = pi.getNextWatchEqc();
    }
    if (eqc.isNull())
    {
      eqc = d_state.getSink();
    }
    else
    {
      success = true;
    }
    assignment.push_back(eqc);
  }
  if (!success)
  {
    return false;
  }
  // assign each variable
  for (size_t i = 0, nvars = slevel.d_varsToAssign.size(); i < nvars; i++)
  {
    assignVar(slevel.d_varsToAssign[i], assignment[i]);
  }

  return true;
}

bool InstDriver::processMatcher(QuantInfo& qi, TNode matcher)
{
  TypeNode tn = matcher.getType();
  // get constraints to determine initial equivalence classes
  const std::map<TNode, std::vector<Node>>& cs = qi.getConstraints();
  TNode eq;
  std::vector<TNode> deq;
  std::map<TNode, std::vector<Node>>::const_iterator itc = cs.find(matcher);
  if (itc != cs.end())
  {
    bool setInactive = false;
    for (const Node& cc : itc->second)
    {
      if (cc.isNull())
      {
        // constraint says that the term must be equal to anything
        continue;
      }
      TNode dval;
      if (QuantInfo::isDeqConstraint(cc, matcher, dval))
      {
        Assert(!tn.isBoolean());
        Assert(!dval.isNull());
        dval = d_state.getGroundRepresentative(dval);
        if (!dval.isNull())
        {
          if (eq.isNull())
          {
            deq.push_back(dval);
          }
          else if (eq == dval)
          {
            // term must be equal and disequal to the same thing
            setInactive = true;
          }
        }
        else
        {
          // the pattern needs to be disequal to a term that does not exist
          setInactive = true;
        }
      }
      else
      {
        TNode eval = d_state.getGroundRepresentative(cc);
        if (!eval.isNull())
        {
          if (eq.isNull())
          {
            // also check if disequality constraints contradict
            if (std::find(deq.begin(), deq.end(), eq) != deq.end())
            {
              // term must be equal and disequal to the same thing
              setInactive = true;
            }
            else
            {
              eq = eval;
            }
            deq.clear();
          }
          else if (eval != eq)
          {
            // Matcher needs to be equal to two different things that are not
            // equal. This should happen very infrequently, e.g.
            // forall x. (f(x) = a ^ f(x) = b) => P(x) where a is not currently
            // equal to b.
            setInactive = true;
          }
        }
        else
        {
          // the pattern needs to be equal to a term that does not exist
          setInactive = true;
        }
      }
      if (setInactive)
      {
        d_state.setQuantInactive(qi);
        return false;
      }
    }
  }
  // if we have an equality constraint, we limit to matching in that equivalence
  // class
  PatTermInfo& pi = d_state.getPatTermInfo(matcher);
  if (!eq.isNull())
  {
    Assert(d_state.isGroundEqc(eq));
    pi.addWatchEqc(eq);
  }
  else
  {
    // otherwise, we must consider all equivalence clases
    if (tn.isBoolean())
    {
      Assert(deq.empty());
      pi.addWatchEqc(d_true);
      pi.addWatchEqc(d_false);
    }
    else
    {
      // if not Boolean, we can filter by deq
      const std::unordered_set<TNode>& eqcs = d_state.getGroundEqcFor(tn);
      for (TNode eqc : eqcs)
      {
        if (std::find(deq.begin(), deq.end(), eqc) == deq.end())
        {
          pi.addWatchEqc(eqc);
        }
      }
    }
  }
  // now run matching
  runMatching(pi);
  return true;
}

void InstDriver::runMatching(PatTermInfo& pi)
{
  TNode op = pi.d_matchOp;
  if (op.isNull())
  {
    // if not a matchable operator
    return;
  }
  Assert(pi.d_pattern.getNumChildren() > 0);
  std::vector<TNode> pargs;
  // get the status of the arguments of pi
  for (TNode pic : pi.d_pattern)
  {
  }

  std::unordered_map<TNode, std::vector<Node>>::iterator itm;
  TNode weqc = pi.getNextWatchEqc();
  while (!weqc.isNull())
  {
    Assert(d_state.isGroundEqc(weqc));
    MatchEqcInfo& meqc = d_state.getMatchEqcInfo(weqc);
    // increment weqc to the next equivalence class
    weqc = pi.getNextWatchEqc();

    // get the terms to match in this equivalence class
    itm = meqc.d_matchOps.find(op);
    if (itm == meqc.d_matchOps.end())
    {
      // none in this equivalence class
      continue;
    }
    //
  }
}

bool InstDriver::isFinished() const { return d_state.isFinished(); }

void InstDriver::assignVar(TNode v, TNode eqc)
{
  Assert(d_qstate.getEqualityEngine()->consistent());
  if (d_state.isSink(eqc))
  {
    // notify the state
    d_state.notifyPatternSink(v);
  }
  else
  {
    Assert(v.getType().isComparableTo(eqc.getType()));
    // assert to the equality engine
    Node eq = v.eqNode(eqc);
    d_qstate.getEqualityEngine()->assertEquality(eq, true, eq);
    // should still be consistent
    Assert(d_qstate.getEqualityEngine()->consistent());
  }
}

SearchLevel& InstDriver::getSearchLevel(size_t i) { return d_levels[i]; }

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
