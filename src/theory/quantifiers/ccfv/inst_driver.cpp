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

namespace cvc5 {
namespace theory {
namespace quantifiers {

InstDriver::InstDriver(Env& env,
                    QuantifiersState& qs,
                    QuantifiersInferenceManager& qim,
                    QuantifiersRegistry& qr,
                    TermRegistry& tr)
{
}

QuantInfo& InstDriver::getQuantInfo(TNode q)
{
  std::map<Node, QuantInfo>::iterator it = d_quantInfo.find(q);
  Assert (it!=d_quantInfo.end());
  return it->second;
}

FreeVarInfo& InstDriver::getFreeVarInfo(TNode v)
{
  std::map<Node, FreeVarInfo>::iterator it = d_fvInfo.find(v);
  Assert (it!=d_fvInfo.end());
  return it->second;
}

PatTermInfo& InstDriver::getPatTermInfo(TNode p)
{
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  Assert (it!=d_pInfo.end());
  return it->second;
}

EqcInfo& InstDriver::getEqcInfo(TNode r)
{
  std::map<Node, EqcInfo>::iterator it = d_eqcInfo.find(r);
  Assert (it!=d_eqcInfo.end());
  return it->second;
}
  
bool InstDriver::eqNotifyTriggerPredicate(TNode predicate, bool value)
{
  // use this?
  return true;
}

bool InstDriver::eqNotifyTriggerTermEquality(TheoryId tag,
                                             TNode t1,
                                             TNode t2,
                                             bool value)
{
  // use this?
  return true;
}

void InstDriver::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  // should never happen
  Assert(false);
}

void InstDriver::eqNotifyNewClass(TNode t)
{
  // do nothing
}

void InstDriver::eqNotifyMerge(TNode t1, TNode t2)
{
  if (d_groundEqc.find(t1) != d_groundEqc.end())
  {
    // should never merge ground equivalence classes
    Assert(d_groundEqc.find(t2) == d_groundEqc.end());
    // swap
    std::swap(t1, t2);
  }
  else if (d_groundEqc.find(t2) != d_groundEqc.end())
  {
    // update the list of ground equivalence classes, which is overapproximated
    // i.e. we do not remove t2
    d_state.d_groundEqc.insert(t1);
  }
  else
  {
    // two patterns merging, track the list
    EqcInfo* eq2 = getOrMkEqcInfo(t2);
    EqcInfo* eq1 = getOrMkEqcInfo(t1, true);
    eq1->d_eqPats.insert(t2);
    if (eq2 != nullptr)
    {
      eq1->d_eqPats.insert(eq2->d_eqPats.begin(), eq2->d_eqPats.end());
    }
    return;
  }
  // we are in a situation where a ground equivalence class t2 has merged
  // with a pattern equivalence class.
  // notify the pattern for the representative
  notifyPatternEqGround(t1, t2);
  // if there are patterns equal to this one, notify them too
  EqcInfo* eq = getOrMkEqcInfo(t1);
  if (eq != nullptr)
  {
    for (TNode t : d_state.d_eqPats)
    {
      notifyPatternEqGround(t, t2);
    }
  }
}

void InstDriver::notifyPatternEqGround(TNode p, TNode g)
{
  const PatTermInto& pti = getPatternTermInfo(p);
  // if still active
  if (!pti.d_isActive)
  {
    return;
  }
  pti.d_isActive = false;
  for (size_t i = 0; i < 2; i++)
  {
    const std::map<const TNode, std::vector<TNode> >& req =
        i == 0 ? pti.d_gEqReq : pti.d_gDeqReq;
    bool processEq = (i == 0);
    for (const std::pair<const TNode, std::vector<TNode> >& r : req)
    {
      Assert(r.first.isNull() || d_equalityEngine.hasTerm(r.first));
      if (!g.isNull())
      {
        if (!r.first.isNull()
            || (d_equalityEngine.getRepresentative(r.first) == g) == processEq)
        {
          // the required constraint was satisfied, do not mark dead
          continue;
        }
      }
      // mark all as dead
      for (TNode n : r.second)
      {
        // parent could be a quantified formula
        if (n.getKind() == FORALL)
        {
          // notify dead
        }
        else
        {
          eqNotifyPatternEqGround(n, Node::null());
        }
      }
    }
  }
}

void InstDriver::notifyQuantMatch(TNode q, bool success)
{
  QuantInfo& qi = getQuantInfo(q);
  if (!qi.d_isActive)
  {
    return;
  }
  if (!success)
  {
    qi.d_isActive = false;
    return;
  }
  // update watched matcher?
}

void InstDriver::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  // should never happen
  Assert(false);
}

void InstDriver::check()
{
  // TODO
  do
  {
    TNode v = getNextVariable();
    if (!v.isNull())
    {
      decideVar(v);
    }
    // otherwise increment current
  } while (!d_stack.empty());
}

bool InstDriver::isFinished() const { return false; }

TNode InstDriver::getNextVariable() {}

void InstDriver::pushVar(TNode v)
{
  // push a context
  // context().push();
  d_varStack.push_back(v);

  const FreeVarInfo& fvi = getFreeVarInfo(v);
  fvi.resetDomain();

  // compute the equivalence classes we should assign
  // compute d_eqcDomain
  // TODO: based on top-down matching?

  // decrement the # assigned variables in each term that contains it, which
  // also computes which terms are newly fully assigned. These are stored in
  // d_fullyAssignedPat.
  for (TNode pat : fvi.d_useList)
  {
    const PatTermInto& pti = getPatternTermInfo(p);
    Assert(pti.d_numUnassignVar > 0);
    pti.d_numUnassignVar = pti.d_numUnassignVar - 1;
    if (pti.d_numUnassignVar == 0)
    {
      fvi.d_fullyAssignedPat.push_back(pat);
    }
  }
}

void InstDriver::popVar()
{
  Assert(!d_varStack.empty());

  TNode v = d_varStack.back();

  d_varStack.pop_back();
}

void InstDriver::assignVar(TNode v,
                           TNode eqc,
                           std::vector<TNode>& fullyAssignedPats)
{
  Node eq = v.eqNode(eqc);
  d_ee->assertEquality(eq);
  // may be finished
  if (isFinished())
  {
    return;
  }
  const FreeVarInfo& fvi = getFreeVarInfo(v);
  // for each fully assigned pattern, if they are not fully assigned, we mark
  // them as dead
  for (TNode p : fvi.d_fullAssignedPats)
  {
    notifyPatternEqGround(p, d_null);
    // if all quantified formulas are inactive, finish
    if (isFinished())
    {
      break;
    }
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
