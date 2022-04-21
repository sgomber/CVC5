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

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ccfv {

State::State(Env& env, QuantifiersState& qs, TermDb* tdb)
    : EnvObj(env),
      d_qstate(qs),
      d_tdb(tdb),
      d_notifyActive(context(), false),
      d_numActiveQuant(context(), 0),
      d_keep(context())
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  d_none = sm->mkDummySkolem("none", nm->booleanType());
  d_some = sm->mkDummySkolem("some", nm->booleanType());
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

bool State::isFinished() const { return d_numActiveQuant == 0; }

void State::resetRound(size_t nquant)
{
  Assert(!d_notifyActive);
  // We are actively getting notifications in this context. This is set within
  // a local context push in the InstDriver and does not need to be reset to
  // false.
  d_notifyActive = true;
  // reset the search state
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  if (TraceIsOn("ccfv-matching"))
  {
    Trace("ccfv-matching") << "E-graph:" << std::endl;
    Trace("ccfv-matching") << ee->debugPrintEqc() << std::endl;
  }
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  d_groundEqc.clear();
  d_typeGroundEqc.clear();
  // matching information is not maintained incrementally
  d_meqcInfo.clear();
  // for Boolean, true/false are always the ground equivalence classes
  d_groundEqc.insert(d_true);
  d_groundEqc.insert(d_false);
  std::map<TypeNode, NodeSet>::iterator itt;
  while (!eqcs_i.isFinished())
  {
    TNode r = *eqcs_i;
    ++eqcs_i;
    TypeNode tn = r.getType();
    if (tn.isBoolean())
    {
      // skip Boolean equivalence classes
      continue;
    }
    if (expr::hasBoundVar(r))
    {
      // skip pattern terms
      continue;
    }
    d_groundEqc.insert(r);
    d_typeGroundEqc[tn].insert(r);
  }
  d_numActiveQuant = nquant;

  // reset round on pattern infos
  for (std::pair<const Node, PatTermInfo>& p : d_pInfo)
  {
    p.second.resetRound();
  }

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

QuantInfo& State::initializeQuantInfo(TNode q, expr::TermCanonize& tc)
{
  std::map<Node, QuantInfo>::iterator it = d_quantInfo.find(q);
  if (it == d_quantInfo.end())
  {
    d_quantInfo.emplace(q, context());
    it = d_quantInfo.find(q);
    // initialize
    it->second.initialize(q, d_tdb, d_qstate.getEqualityEngine(), tc);
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

FreeVarInfo& State::getFreeVarInfo(TNode v)
{
  std::map<Node, FreeVarInfo>::iterator it = d_fvInfo.find(v);
  Assert(it != d_fvInfo.end());
  return it->second;
}

PatTermInfo& State::getOrMkPatTermInfo(TNode p)
{
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  if (it == d_pInfo.end())
  {
    it = d_pInfo.emplace(p, context()).first;
    // initialize the pattern
    it->second.initialize(p, d_qstate.getEqualityEngine(), d_tdb);
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

void State::eqNotifyMerge(TNode t1, TNode t2)
{
  if (!d_notifyActive)
  {
    // we are not notify active. This is called when equivalence classes
    // merge outside of when we are running CCFV.
    return;
  }
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

void State::notifyPatternNone(TNode p) { notifyPatternEqGround(p, d_none); }

void State::notifyPatternEqGround(TNode p, TNode g)
{
  Assert(!g.isNull());
  Assert(isGroundEqc(g) || isNone(g));
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  Assert(it != d_pInfo.end());
  if (!it->second.isActive())
  {
    // already assigned
    return;
  }
  Trace("ccfv-state-debug")
      << "Notify pattern eq ground: " << p << " == " << g << std::endl;
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
    // notify the ordinary parents always, notify the congruence parents if none
    size_t maxIter = 1;
    if (isNone(g))
    {
      maxIter = 2;
    }
    else if (it->second.d_isWatchedEval.get())
    {
      Trace("ccfv-state-debug")
          << "Notify assert " << p << " == " << g << std::endl;
      // if it is a watched evaluate term, assert the equality here
      assertEquality(p, g);
    }
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
        if (it->second.notifyChild(*this, p, g))
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
  Trace("ccfv-state-debug") << "Notify quant constraint " << q.getId() << " "
                            << p << " == " << val << std::endl;
  Assert(d_numActiveQuant.get() > 0);
  // check whether we should set inactive
  bool setInactive = false;
  if (isNone(val))
  {
    setInactive = true;
    Trace("ccfv-state-debug") << "...inactive due to none" << std::endl;
  }
  else
  {
    // Are we the "some" val? This is true for predicates whose value is
    // a predicate e.g. equality applied to existing terms.
    bool valSome = isSome(val);
    const std::map<TNode, std::vector<Node>>& cs = qi.getConstraints();
    std::map<TNode, std::vector<Node>>::const_iterator itm = cs.find(p);
    if (itm != cs.end())
    {
      for (TNode c : itm->second)
      {
        if (c.isNull())
        {
          // the constraint said you must be disequal to none, i.e. we must be
          // equal to something. we are ok
          continue;
        }
        else if (valSome)
        {
          // it has the "some" value, and we have any constraint, we remain
          // active but are not strictly a conflict
          qi.setNoConflict();
          Trace("ccfv-state-debug") << "...no conflict" << std::endl;
          break;
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
          Trace("ccfv-state-debug")
              << "...inactive due to constraint " << c << std::endl;
          setInactive = true;
          break;
        }
        else
        {
          Trace("ccfv-state-debug")
              << "...satisfied constraint " << c << std::endl;
        }
      }
    }
    else
    {
      Trace("ccfv-state-debug") << "...no constraints" << std::endl;
    }
  }
  // if we should set inactive, update qi and decrement d_numActiveQuant
  if (setInactive)
  {
    setQuantInactive(qi);
  }
  else
  {
    Trace("ccfv-state-debug") << "...still active" << std::endl;
  }
  // otherwise, we could have an instantiation, but we do not check for this
  // here; instead this is handled based on watching the number of free
  // variables assigned.
}

void State::setQuantInactive(QuantInfo& qi)
{
  if (qi.isActive())
  {
    qi.setActive(false);
    d_numActiveQuant = d_numActiveQuant - 1;
  }
}

void State::assertEquality(TNode p, TNode g)
{
  Trace("ccfv-state-assert") << "Assert: " << p << " == " << g << std::endl;
  Assert(d_qstate.getEqualityEngine()->consistent());
  Assert(!isNone(g));
  Assert(p.getType().isComparableTo(g.getType()));
  // assert to the equality engine
  Node eq = p.eqNode(g);
  d_keep.insert(eq);
  d_qstate.getEqualityEngine()->assertEquality(eq, true, eq);
  // should still be consistent
  Assert(d_qstate.getEqualityEngine()->consistent());
}

Node State::getNone() const { return d_none; }

bool State::isNone(TNode n) const { return n == d_none; }

Node State::getSome() const { return d_some; }

bool State::isSome(TNode n) const { return n == d_some; }

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

bool State::areDisequal(TNode a, TNode b) const
{
  return d_qstate.areDisequal(a, b);
}

Node State::doRewrite(Node n) { return rewrite(n); }

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
  // all pattern terms should have been assigned pattern term info
  Assert(!expr::hasBoundVar(p));
  // use equality engine, go to none if not a part of equivalence classes
  TNode r = getGroundRepresentative(p);
  if (r.isNull())
  {
    return d_none;
  }
  return r;
}

std::string State::toString() const
{
  std::stringstream ss;
  ss << "#groundEqc = " << d_groundEqc.size() << std::endl;
  ss << "#matchEqc = " << d_meqcInfo.size() << std::endl;
  ss << "#eqcInfo = " << d_eqcInfo.size() << std::endl;
  ss << "#patterns = " << d_pInfo.size() << std::endl;
  ss << "#freeVars = " << d_fvInfo.size() << std::endl;
  ss << "#quants = " << d_numActiveQuant.get() << " / " << d_quantInfo.size()
     << std::endl;
  return ss.str();
}

std::string State::toStringSearch() const
{
  std::stringstream ss;
  ss << "activeQuants = " << d_numActiveQuant.get();
  return ss.str();
}

std::string State::toStringDebugSearch() const
{
  std::stringstream ss;
  ss << "activeQuants = " << d_numActiveQuant.get() << "[";
  size_t nqc = 0;
  for (const std::pair<const Node, QuantInfo>& q : d_quantInfo)
  {
    if (q.second.isActive())
    {
      ss << " " << q.first.getId();
      nqc++;
    }
  }
  ss << " ]";
  AlwaysAssert(nqc == d_numActiveQuant.get())
      << "Active quant mismatch " << ss.str();
  return ss.str();
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
