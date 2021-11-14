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
 * State for congruence closure with free variables
 */

#include "theory/quantifiers/ccfv/state.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/uf/equality_engine_iterator.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

State::State(Env& env, QuantifiersState& qs)
    : EnvObj(env),
      d_qstate(qs),
      // d_groundEqc(context()),
      d_numActiveQuant(context(), 0)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  d_sink = sm->mkDummySkolem("sink", nm->booleanType());
}

bool State::isFinished() const { return d_numActiveQuant == 0; }

void State::resetRound()
{
  // get the ground equivalence classes
  d_groundEqc.clear();
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  while (!eqcs_i.isFinished())
  {
    d_groundEqc.insert(*eqcs_i);
    ++eqcs_i;
  }
  // clear the equivalence class info
  d_eqcInfo.clear();
  // TODO: activate the quantified formulas
}

QuantInfo& State::getOrMkQuantInfo(TNode q, expr::TermCanonize& tc)
{
  std::map<Node, QuantInfo>::iterator it = d_quantInfo.find(q);
  if (it == d_quantInfo.end())
  {
    d_quantInfo.emplace(q, context());
    it = d_quantInfo.find(q);
    // initialize
    it->second.initialize(q, tc);
  }
  return it->second;
}

QuantInfo& State::getQuantInfo(TNode q)
{
  std::map<Node, QuantInfo>::iterator it = d_quantInfo.find(q);
  Assert(it != d_quantInfo.end());
  return it->second;
}

FreeVarInfo& State::getOrMkFreeVarInfo(TNode v) { return d_fvInfo[v]; }

const FreeVarInfo& State::getFreeVarInfo(TNode v) const
{
  std::map<Node, FreeVarInfo>::const_iterator it = d_fvInfo.find(v);
  Assert(it != d_fvInfo.end());
  return it->second;
}

PatTermInfo& State::getOrMkPatTermInfo(TNode p)
{
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  if (it == d_pInfo.end())
  {
    d_pInfo.emplace(p, context());
    it = d_pInfo.find(p);
    // initialize the pattern
    it->second.initialize(p);
  }
  return it->second;
}

PatTermInfo& State::getPatTermInfo(TNode p)
{
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  Assert(it != d_pInfo.end());
  return it->second;
}

EqcInfo* State::getOrMkEqcInfo(TNode r, bool doMk)
{
  std::map<Node, EqcInfo>::iterator it = d_eqcInfo.find(r);
  if (it == d_eqcInfo.end())
  {
    if (!doMk)
    {
      return nullptr;
    }
    d_eqcInfo.emplace(r, context());
    it = d_eqcInfo.find(r);
  }
  return &it->second;
}

bool State::eqNotifyTriggerPredicate(TNode predicate, bool value)
{
  // use this?
  return true;
}

bool State::eqNotifyTriggerTermEquality(TheoryId tag,
                                        TNode t1,
                                        TNode t2,
                                        bool value)
{
  // use this?
  return true;
}

void State::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  // should never happen
  Assert(false);
}

void State::eqNotifyNewClass(TNode t)
{
  // do nothing
}

void State::eqNotifyMerge(TNode t1, TNode t2)
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
    d_groundEqc.insert(t1);
  }
  else
  {
    // two patterns merging, track the list
    EqcInfo* eq2 = getOrMkEqcInfo(t2);
    EqcInfo* eq1 = getOrMkEqcInfo(t1, true);
    eq1->d_eqPats.push_back(t2);
    if (eq2 != nullptr)
    {
      for (const Node& n : eq2->d_eqPats)
      {
        eq1->d_eqPats.push_back(n);
      }
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
    for (TNode t : eq->d_eqPats)
    {
      notifyPatternEqGround(t, t2);
    }
  }
}

void State::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  // should never happen
  Assert(false);
}

bool State::notifyChild(PatTermInfo& pi, TNode child, TNode val)
{
  if (!pi.isActive())
  {
    // already set
    return false;
  }
  // if a Boolean connective, handle short circuiting
  if (pi.d_isBooleanConnective)
  {
    if (!isSink(val))
    {
      Assert(val.getKind() == CONST_BOOLEAN);
      bool pol = val.getConst<bool>();
      Kind k = pi.d_pattern.getKind();
      Assert(k != IMPLIES && k != XOR);
      if ((k == AND && !pol) || (k == OR && pol))
      {
        // the value determines the value of this
        pi.d_eq = val;
        return true;
      }
      if (k == ITE)
      {
        // if the condition is being set, and the branch already has a value,
        // then this has the value of the branch.
        if (pi.d_pattern[0] == child)
        {
          Node vbranch = getValue(pi.d_pattern[pol ? 1 : 2]);
          if (!vbranch.isNull())
          {
            pi.d_eq = vbranch;
            return true;
          }
        }
        else
        {
          // if the branch is being set, the condition is determined, and it is
          // the relevant branch, then this value is val.
          Node vcond = getValue(pi.d_pattern[0]);
          if (!vcond.isNull() && vcond.isConst())
          {
            if (child == pi.d_pattern[vcond.getConst<bool>() ? 1 : 2])
            {
              pi.d_eq = val;
              return true;
            }
          }
        }
      }
    }
  }
  else
  {
    // if the value of a child is unknown, we are now unknown
    if (isSink(val))
    {
      pi.d_eq = val;
      return true;
    }
  }
  // set to unknown, handle cases
  pi.d_eq = d_sink;
  // if a Boolean connective, we can possibly evaluate
  if (pi.d_isBooleanConnective)
  {
    Assert(pi.d_numUnassigned.get() > 0);
    pi.d_numUnassigned = pi.d_numUnassigned.get() - 1;
    if (pi.d_numUnassigned == 0)
    {
      NodeManager* nm = NodeManager::currentNM();
      Kind k = pi.d_pattern.getKind();
      Assert(k != IMPLIES && k != XOR);
      if (k == AND || k == OR)
      {
        for (TNode pc : pi.d_pattern)
        {
          TNode cvalue = getValue(pc);
          if (isSink(cvalue))
          {
            // unknown, we are done
            return true;
          }
        }
        pi.d_eq = nm->mkConst(k == AND);
      }
      else
      {
        TNode cval1 = getValue(pi.d_pattern[0]);
        Assert(!cval1.isNull());
        Assert(cval1.isConst() || isSink(cval1));
        if (k == NOT)
        {
          if (cval1.isConst())
          {
            pi.d_eq = nm->mkConst(!cval1.getConst<bool>());
          }
        }
        else if (k == ITE)
        {
          if (cval1.isConst())
          {
            // if condition evaluates, get value of branch
            pi.d_eq = getValue(pi.d_pattern[cval1.getConst<bool>() ? 1 : 2]);
          }
          else
          {
            // otherwise, we only are known if the branches are equal
            TNode cval2 = getValue(pi.d_pattern[1]);
            Assert(!cval2.isNull());
            if (cval2.isConst() && cval2 == getValue(pi.d_pattern[2]))
            {
              pi.d_eq = cval2;
            }
          }
        }
        else
        {
          Assert(k != EQUAL);
          if (cval1.isConst())
          {
            TNode cval2 = getValue(pi.d_pattern[0]);
            Assert(!cval2.isNull());
            if (cval2.isConst())
            {
              // if both side evaluate, we evaluate
              pi.d_eq = nm->mkConst(cval1 == cval2);
            }
          }
        }
      }
      return true;
    }
  }
  return false;
}

void State::notifyPatternEqGround(TNode p, TNode g)
{
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  Assert(it != d_pInfo.end());
  Assert(it->second.isActive());
  it->second.d_eq = g;
  // run notifications until fixed point
  size_t tnIndex = 0;
  std::vector<std::map<Node, PatTermInfo>::iterator> toNotify;
  toNotify.push_back(it);
  while (tnIndex < toNotify.size())
  {
    it = toNotify[tnIndex];
    ++tnIndex;
    p = it->second.d_pattern;
    g = it->second.d_eq;
    // notify the ordinary parents always, notify the congruence parents if sink
    size_t maxIter = isSink(g) ? 2 : 1;
    for (size_t i = 0; i < maxIter; i++)
    {
      context::CDList<Node>& notifyList =
          i == 0 ? it->second.d_parentNotify : it->second.d_parentCongNotify;
      for (TNode pp : notifyList)
      {
        if (pp.getKind() == FORALL)
        {
          // quantified formulas are ordinary parents
          Assert(i == 0);
          // if we have a quantified formula as a parent, notify is a special
          // method, which will test the constraints
          notifyQuant(pp, p, g);
          // could be finished now
          if (isFinished())
          {
            break;
          }
          continue;
        }
        // otherwise, notify the parent
        it = d_pInfo.find(pp);
        Assert(it != d_pInfo.end());
        if (notifyChild(it->second, p, g))
        {
          toNotify.push_back(it);
        }
      }
    }
  }
}

void State::notifyQuant(TNode q, TNode p, TNode val)
{
  Assert(q.getKind() == FORALL);
  QuantInfo& qi = getQuantInfo(q);
  if (!qi.isActive())
  {
    // quantified formula is already inactive
    return;
  }
  Assert(d_numActiveQuant.get() > 0);
  // check whether we should set inactive
  bool setInactive = false;
  if (isSink(val))
  {
    setInactive = true;
  }
  else
  {
    const std::map<TNode, std::vector<Node>>& cs = qi.getMatchConstraints();
    std::map<TNode, std::vector<Node>>::const_iterator itm = cs.find(val);
    if (itm != cs.end())
    {
      for (TNode c : itm->second)
      {
        if (c.isNull())
        {
          // the constraint said you must be disequal to sink, i.e. we must be
          // equal to something. we are ok
          continue;
        }
        // if a disequality constraint
        bool isEq = true;
        if (c.getKind() == NOT)
        {
          Assert(c[0].getKind() == EQUAL);
          isEq = false;
          c = c[0][1];
        }
        // otherwise check the constraint
        TNode r = d_qstate.getRepresentative(c);
        if (isEq != (val == r))
        {
          setInactive = true;
          break;
        }
      }
    }
  }
  // if we should set inactive, update qi and decrement d_numActiveQuant
  if (setInactive)
  {
    qi.setActive(false);
    d_numActiveQuant = d_numActiveQuant - 1;
  }
  // otherwise, we could have an instantiation, but we do not check for this
  // here; instead this is handled based on watching the number of free
  // variables assigned.
}

Node State::getSink() const { return d_sink; }

bool State::isSink(TNode n) const { return n == d_sink; }

TNode State::getValue(TNode p) const
{
  std::map<Node, PatTermInfo>::const_iterator it = d_pInfo.find(p);
  if (it != d_pInfo.end())
  {
    return it->second.d_eq;
  }
  Assert(!expr::hasFreeVar(p));
  // use equality engine, go to sink if not a part of equivalence classes
  TNode r = d_qstate.getRepresentative(p);
  if (d_groundEqc.find(r) != d_groundEqc.end())
  {
    return r;
  }
  return d_sink;
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
