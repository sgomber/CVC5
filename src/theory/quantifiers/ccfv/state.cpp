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

State::State(Env& env, QuantifiersState& qs, TermDb* tdb)
    : EnvObj(env), d_qstate(qs), d_tdb(tdb), d_numActiveQuant(context(), 0)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  d_sink = sm->mkDummySkolem("sink", nm->booleanType());
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

bool State::isFinished() const { return d_numActiveQuant == 0; }

void State::resetRound(size_t nquant)
{
  // reset the search state
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  d_groundEqc.clear();
  d_typeGroundEqc.clear();
  // for Boolean, true/false are always the ground equivalence classes
  d_groundEqc.insert(d_true);
  d_groundEqc.insert(d_false);
  std::map<TypeNode, NodeSet>::iterator itt;
  while (!eqcs_i.isFinished())
  {
    TNode r = *eqcs_i;
    TypeNode tn = r.getType();
    if (tn.isBoolean())
    {
      // skip Boolean equivalence classes
      continue;
    }
    d_groundEqc.insert(r);
    d_typeGroundEqc[tn].insert(r);
    ++eqcs_i;
  }
  d_numActiveQuant = nquant;

  // clear the equivalence class info?
  // NOTE: if we are adding terms when quantified formulas are asserted, then
  // we should not clear the equivalence class information here.
  // d_eqcInfo.clear();
  // reset free variable information
  /*
  for (std::pair<const Node, FreeVarInfo>& fi : d_fvInfo)
  {
    fi.second.resetRound();
  }
  */
}

QuantInfo& State::initializeQuantInfo(TNode q,
                                      eq::EqualityEngine* ee,
                                      expr::TermCanonize& tc)
{
  std::map<Node, QuantInfo>::iterator it = d_quantInfo.find(q);
  if (it == d_quantInfo.end())
  {
    d_quantInfo.emplace(q, context());
    it = d_quantInfo.find(q);
    // initialize
    it->second.initialize(q, ee, tc);
  }
  return it->second;
}

QuantInfo& State::getQuantInfo(TNode q)
{
  std::map<Node, QuantInfo>::iterator it = d_quantInfo.find(q);
  Assert(it != d_quantInfo.end());
  return it->second;
}

FreeVarInfo& State::getOrMkFreeVarInfo(TNode v)
{
  std::map<Node, FreeVarInfo>::iterator it = d_fvInfo.find(v);
  if (it == d_fvInfo.end())
  {
    d_fvInfo.emplace(v, context());
    it = d_fvInfo.find(v);
  }
  return it->second;
}

const FreeVarInfo& State::getFreeVarInfo(TNode v) const
{
  std::map<Node, FreeVarInfo>::const_iterator it = d_fvInfo.find(v);
  Assert(it != d_fvInfo.end());
  return it->second;
}

std::vector<TNode> State::getFreeVarList() const
{
  std::vector<TNode> fvar;
  for (const std::pair<const Node, FreeVarInfo>& fi : d_fvInfo)
  {
    if (!fi.second.isActive())
    {
      fvar.push_back(fi.first);
    }
  }
  return fvar;
}

bool sortVarNQuant(const std::pair<size_t, TNode>& a,
                   const std::pair<size_t, TNode>& b)
{
  if (a.first > b.first)
  {
    return true;
  }
  return a.first == b.first && a.second < b.second;
}

/*
std::vector<TNode> State::getOrderedFreeVarList() const
{
  std::vector<std::pair<size_t, TNode>> fvarList;
  for (const std::pair<const Node, FreeVarInfo>& fi : d_fvInfo)
  {
    size_t nquant = fi.second.d_quantList.size();
    if (nquant > 0)
    {
      fvarList.push_back(std::pair<size_t, TNode>(nquant, fi.first));
    }
  }
  // sort by most quantifiers first
  std::sort(fvarList.begin(), fvarList.end(), sortVarNQuant);
  std::vector<TNode> fvar;
  for (const std::pair<size_t, TNode>& v : fvarList)
  {
    fvar.push_back(v.second);
  }
  return fvar;
}
*/

PatTermInfo& State::getOrMkPatTermInfo(TNode p)
{
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  if (it == d_pInfo.end())
  {
    it = d_pInfo.emplace(p, context()).first;
    // initialize the pattern
    it->second.initialize(p, d_tdb);
  }
  return it->second;
}

PatTermInfo& State::getPatTermInfo(TNode p)
{
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  Assert(it != d_pInfo.end());
  return it->second;
}

MatchEqcInfo& State::getMatchEqcInfo(TNode r)
{
  Assert(isGroundEqc(r));
  std::map<Node, MatchEqcInfo>::iterator it = d_meqcInfo.find(r);
  if (it == d_meqcInfo.end())
  {
    MatchEqcInfo& meqc = d_meqcInfo[r];
    // initialize the match information
    meqc.initialize(r, *this, d_qstate.getEqualityEngine(), d_tdb);
    return meqc;
  }
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
const EqcInfo* State::getEqcInfo(TNode r) const
{
  std::map<Node, EqcInfo>::const_iterator it = d_eqcInfo.find(r);
  if (it == d_eqcInfo.end())
  {
    return nullptr;
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
  // constants always remain representatives
  Assert(!t2.isConst());
  EqcInfo* eq1 = nullptr;
  if (isGroundEqc(t1))
  {
    // should never merge ground equivalence classes
    Assert(!isGroundEqc(t2));
    // swap
    std::swap(t1, t2);
  }
  else if (isGroundEqc(t2))
  {
    // update the list of ground equivalence classes, which is overapproximated
    // i.e. we do not remove t2
    eq1 = getOrMkEqcInfo(t1, true);
    eq1->d_groundEqc = t2;
  }
  else
  {
    // two patterns merging, track the list
    eq1 = getOrMkEqcInfo(t1, true);
    EqcInfo* eq2 = getOrMkEqcInfo(t2);
    if (eq2 != nullptr)
    {
      if (!eq2->d_groundEqc.get().isNull())
      {
        // an equivalence class whose representative is a pattern that was
        // already made equal to a ground equivalence class
        t2 = eq2->d_groundEqc.get();
        eq1->d_groundEqc = t2;
      }
      else
      {
        // track that the pattern and all patterns made equal to it are
        // equivalent
        for (const Node& n : eq2->d_eqPats)
        {
          eq1->d_eqPats.push_back(n);
        }
        eq1->d_eqPats.push_back(t2);
        return;
      }
    }
    else
    {
      // track that the pattern is equivalent
      eq1->d_eqPats.push_back(t2);
      return;
    }
  }
  Assert(isGroundEqc(t2));
  // we are in a situation where a ground equivalence class t2 has merged
  // with a pattern equivalence class.
  // notify the pattern for the representative
  notifyPatternEqGround(t1, t2);
  // if there are patterns equal to this one, notify them too
  if (eq1 == nullptr)
  {
    eq1 = getOrMkEqcInfo(t1);
  }
  if (eq1 != nullptr)
  {
    for (TNode t : eq1->d_eqPats)
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

void State::notifyPatternSink(TNode p) { notifyPatternEqGround(p, d_sink); }

bool State::notifyChild(PatTermInfo& pi, TNode child, TNode val)
{
  Assert(isGroundEqc(val) || isSink(val));
  if (!pi.isActive())
  {
    // already set
    return false;
  }
  if (pi.d_isBooleanConnective)
  {
    // if a Boolean connective, handle short circuiting if we set a non-sink
    // value
    if (!isSink(val))
    {
      Assert(val.getKind() == CONST_BOOLEAN);
      bool pol = val.getConst<bool>();
      Kind k = pi.d_pattern.getKind();
      // implies and xor are eliminated from quantifier bodies
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
    // if a Boolean connective, we can possibly evaluate
    Assert(pi.d_numUnassigned.get() > 0);
    pi.d_numUnassigned = pi.d_numUnassigned.get() - 1;
    if (pi.d_numUnassigned == 0)
    {
      // set to unknown, handle cases
      pi.d_eq = d_sink;
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
  else
  {
    // if the value of a child is unknown, we are now unknown
    if (isSink(val))
    {
      pi.d_eq = val;
      return true;
    }
  }
  return false;
}

void State::notifyPatternEqGround(TNode p, TNode g)
{
  Assert(!g.isNull());
  Assert(isGroundEqc(g) || isSink(g));
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  Assert(it != d_pInfo.end());
  if(!it->second.isActive())
  {
    // already assigned
    return;
  }
  it->second.d_eq = g;
  // run notifications until fixed point
  size_t tnIndex = 0;
  std::vector<std::map<Node, PatTermInfo>::iterator> toNotify;
  toNotify.push_back(it);
  while (tnIndex < toNotify.size())
  {
    it = toNotify[tnIndex];
    ++tnIndex;
    Assert(it != d_pInfo.end());
    p = it->second.d_pattern;
    g = it->second.d_eq;
    Assert(!g.isNull());
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
        // otherwise, notify the parent pattern
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
    const std::map<TNode, std::vector<Node>>& cs = qi.getConstraints();
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
        TNode dval;
        if (QuantInfo::isDeqConstraint(c, p, dval))
        {
          Assert(c[0].getKind() == EQUAL);
          isEq = false;
          c = dval;
        }
        // otherwise check the constraint
        TNode r = getGroundRepresentative(c);
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
    setQuantInactive(qi);
  }
  // otherwise, we could have an instantiation, but we do not check for this
  // here; instead this is handled based on watching the number of free
  // variables assigned.
}

void State::setQuantInactive(QuantInfo& qi)
{
  Assert(qi.isActive());
  qi.setActive(false);
  d_numActiveQuant = d_numActiveQuant - 1;
}

Node State::getSink() const { return d_sink; }

bool State::isSink(TNode n) const { return n == d_sink; }

const std::unordered_set<TNode>& State::getGroundEqcFor(TypeNode tn) const
{
  std::map<TypeNode, std::unordered_set<TNode>>::const_iterator it =
      d_typeGroundEqc.find(tn);
  if (it == d_typeGroundEqc.end())
  {
    return d_emptyEqc;
  }
  return it->second;
}

bool State::isGroundEqc(TNode r) const
{
  Assert(d_sstate != nullptr);
  return d_groundEqc.find(r) != d_groundEqc.end();
}

TNode State::getGroundRepresentative(TNode n) const
{
  TNode r = d_qstate.getRepresentative(n);
  if (isGroundEqc(r))
  {
    return r;
  }
  // otherwise it may be a pattern that became a representative of an
  // equivalence class?
  const EqcInfo* eq = getEqcInfo(r);
  if (eq == nullptr)
  {
    return TNode::null();
  }
  // check the equivalence class info, which may also be null
  return eq->d_groundEqc.get();
}

bool State::isQuantActive(TNode q) const
{
  std::map<Node, QuantInfo>::const_iterator it = d_quantInfo.find(q);
  Assert(it != d_quantInfo.end());
  return it->second.isActive();
}

TNode State::getValue(TNode p) const
{
  std::map<Node, PatTermInfo>::const_iterator it = d_pInfo.find(p);
  if (it != d_pInfo.end())
  {
    return it->second.d_eq;
  }
  Assert(!expr::hasFreeVar(p));
  // use equality engine, go to sink if not a part of equivalence classes
  TNode r = getGroundRepresentative(p);
  if (r.isNull())
  {
    return d_sink;
  }
  return r;
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
