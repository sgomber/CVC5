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

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

State::State(Env& env, QuantifiersState& qs)
    : EnvObj(env),
      d_qstate(qs),
      d_groundEqc(context()),
      d_numActiveQuant(context(), 0)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  d_sink = sm->mkDummySkolem("sink", nm->booleanType());
}

bool State::isFinished() const { return d_numActiveQuant == 0; }

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

EqcInfo& State::getOrMkEqcInfo(TNode r)
{
  std::map<Node, EqcInfo>::iterator it = d_eqcInfo.find(r);
  if (it == d_eqcInfo.end())
  {
    d_eqcInfo.emplace(r, context());
    it = d_eqcInfo.find(r);
  }
  return it->second;
}

bool State::notify(PatTermInfo& pi, TNode child, TNode val)
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
    // notify the parents always, notify the congruence parents if sink
    size_t maxIter = isSink(g) ? 2 : 1;
    for (size_t i=0; i<maxIter; i++)
    {
      std::vector<TNode>& notifyList = i==0 ? it->second.d_parentNotify : it->second.d_parentCongNotify;
      for (TNode pp : notifyList)
      {
        if (pp.getKind() == FORALL)
        {
          // if we have a quantified formula as a parent, notify
          notifyQuant(pp, p, g);
          if (isFinished())
          {
            // could be finished now
            break;
          }
          continue;
        }
        // otherwise, notify the parent
        it = d_pInfo.find(pp);
        Assert(it != d_pInfo.end());
        if (notify(it->second, p, g))
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
    std::map<TNode, std::vector<Node>>::const_iterator itm;
    for (size_t i = 0; i < 2; i++)
    {
      bool isEq = (i == 0);
      const std::map<TNode, std::vector<Node>>& cs =
          qi.getMatchConstraints(isEq);
      itm = cs.find(val);
      if (itm == cs.end())
      {
        continue;
      }
      for (TNode c : itm->second)
      {
        TNode r = d_qstate.getRepresentative(c);
        if (isEq != (val == r))
        {
          setInactive = true;
          break;
        }
      }
      if (setInactive)
      {
        break;
      }
    }
  }
  if (setInactive)
  {
    qi.setActive(false);
    d_numActiveQuant = d_numActiveQuant - 1;
  }
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
