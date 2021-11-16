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

#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/uf/equality_engine.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

InstDriver::InstDriver(Env& env,
                       State& state,
                       QuantifiersState& qs,
                       QuantifiersInferenceManager& qim,
                       TermRegistry& tr)
    : EnvObj(env),
      d_state(state),
      d_qstate(qs),
      d_qim(qim),
      d_treg(tr),
      d_matching(env, state, qs),
      d_numLevels(0),
      d_keep(context()),
      d_foundInst(false),
      d_inConflict(false)
{
}

void InstDriver::addToEqualityEngine(QuantInfo& qi)
{
  // add the congruence terms to the equality engine
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  Assert(ee->consistent());
  const std::vector<TNode>& pterms = qi.getCongruenceTerms();
  for (TNode p : pterms)
  {
    ee->addTerm(p);
    // should now exist in the equality engine, and not have a value
    Assert(ee->consistent());
    Assert(ee->hasTerm(p));
    Assert(d_state.getValue(p).isNull());
  }
}

void InstDriver::check(const std::vector<TNode>& quants)
{
  Trace("ccfv") << "InstDriver::check" << std::endl;
  // we modify the equality engine, so open a scope
  context()->push();

  // Reset the state. Notice that we must do this before adding pattern terms
  // to the equality engine.
  Trace("ccfv-debug") << "Reset state..." << std::endl;
  d_state.resetRound(quants.size());

  // reset information about whether we have found instantiations
  d_foundInst = false;
  d_inConflict = false;

  // reset round for all quantified formulas
  Trace("ccfv-debug") << "Reset " << quants.size() << " quants..." << std::endl;
  for (TNode q : quants)
  {
    QuantInfo& qi = d_state.getQuantInfo(q);
    qi.resetRound();
    // add congruence terms from quantified formulas to the equality engine
    addToEqualityEngine(qi);
  }

  // do initial notifications for relevant ground terms in the bodies of
  // quantified formulas.
  FreeVarInfo& fiNull = d_state.getOrMkFreeVarInfo(Node::null());
  Trace("ccfv-debug") << "Initial notify " << fiNull.d_useList.size()
                      << " ground terms..." << std::endl;
  for (const Node& t : fiNull.d_useList)
  {
    TNode trep = d_state.getGroundRepresentative(t);
    if (trep.isNull())
    {
      d_state.notifyPatternSink(t);
    }
    else
    {
      d_state.notifyPatternEqGround(t, trep);
    }
  }

  // if not already finished, perform the search over assignments to variables
  if (!isFinished())
  {
    // reset search levels
    // NOTE: could incrementally maintain this?
    Trace("ccfv-debug") << "Reset search levels..." << std::endl;
    resetSearchLevels(quants);
    Trace("ccfv-debug") << "Search..." << std::endl;
    search();
    Trace("ccfv-debug") << "...finished" << std::endl;
  }
  else
  {
    Trace("ccfv-debug") << "...already finished" << std::endl;
  }

  // pop the context
  context()->pop();
}

void InstDriver::resetSearchLevels(const std::vector<TNode>& quants)
{
  // compute the levels at which the variables are at
  d_levels.clear();
  std::map<TNode, std::vector<TNode>> partition;
  std::map<TNode, size_t> fvLevel;
  assignVarsToLevels(0, quants, partition, fvLevel);

  // set the start levels
  std::map<TNode, size_t>::iterator itf;
  for (TNode q : quants)
  {
    QuantInfo& qi = d_state.getQuantInfo(q);
    const std::vector<TNode>& fvs = qi.getOrderedFreeVariables();
    Assert(!fvs.empty());
    itf = fvLevel.find(fvs[0]);
    Assert(itf != fvLevel.end());
    if (itf->second > 0)
    {
      SearchLevel& slevel = getSearchLevel(itf->second - 1);
      slevel.d_startQuants.push_back(q);
    }
  }
  // set that it is the first time seeing each of the levels
  d_numLevels = d_levels.size();
  for (std::pair<const size_t, SearchLevel>& sl : d_levels)
  {
    Assert(sl.first < d_numLevels);
    sl.second.d_firstTime = true;
  }

  if (Trace.isOn("ccfv-debug"))
  {
    for (std::pair<const size_t, SearchLevel>& sl : d_levels)
    {
      Trace("ccfv-debug") << "Search level #" << sl.first << ":" << std::endl;
      Trace("ccfv-debug") << sl.second.toStringDebug() << std::endl;
    }
  }
}

void InstDriver::assignVarsToLevels(
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
    assignVarsToLevels(nextLevel, nextQuants, partition, fvLevel);
  }
}

bool InstDriver::pushLevel(size_t level)
{
  if (level == d_numLevels)
  {
    // already at maximum level
    return false;
  }
  SearchLevel& slevel = getSearchLevel(level);
  bool wasFirstTime = slevel.d_firstTime;
  if (slevel.d_firstTime)
  {
    slevel.d_firstTime = false;
  }
  else
  {
    // if not first time, disable all that start here
    for (TNode q : slevel.d_startQuants)
    {
      QuantInfo& qi = d_state.getQuantInfo(q);
      d_state.setQuantInactive(qi);
    }
    if (d_state.isFinished())
    {
      return false;
    }
  }
  Assert(!slevel.d_varsToAssign.empty());
  // Find the next assignment for each variable. Variables that are at the
  // same level can be assigned in parallel.
  std::vector<TNode> assignment;
  bool success = false;
  // assign all variables in parallel
  for (TNode v : slevel.d_varsToAssign)
  {
    PatTermInfo& pi = d_state.getPatTermInfo(v);
    FreeVarInfo& fi = d_state.getFreeVarInfo(v);
    TNode eqc = pi.getNextWatchEqc();
    while (eqc.isNull())
    {
      // get the next quantified formula containing v
      TNode q = fi.getNextQuantifier();
      if (q.isNull())
      {
        // no more quantifiers to match
        break;
      }
      QuantInfo& qi = d_state.getQuantInfo(q);
      if (!qi.isActive())
      {
        // quantified formula is not active
        continue;
      }
      TNode matcher = qi.getMatcherFor(v);
      if (matcher.isNull())
      {
        // doesn't have a matcher for this variable, continue
        continue;
      }
      if (!d_matching.processMatcher(qi, matcher))
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
  if (!success && !wasFirstTime)
  {
    // Could not find an assignment to any variables, and this was not the
    // first time we ran. In this case, a previous assignment ran strictly
    // more information.
    return false;
  }
  // we push here, since we are updating the state of the equality engine

  context()->push();
  // assign each variable
  for (size_t i = 0, nvars = slevel.d_varsToAssign.size(); i < nvars; i++)
  {
    TNode v = slevel.d_varsToAssign[i];
    TNode eqc = assignment[i];
    if (d_state.isSink(eqc))
    {
      d_state.notifyPatternSink(v);
      // TODO: disable all quantified formulas that contain this variable?
    }
    else
    {
      // otherwise, assert v = eqc to the equality engine
      assignVar(v, eqc);
    }
    if (d_state.isFinished())
    {
      context()->pop();
      return false;
    }
  }

  // assign final terms to sink
  // The use list terms of the variables to assign here are those that are now
  // fully assigned. If these terms have not yet merged, we are done.
  for (TNode v : slevel.d_varsToAssign)
  {
    const FreeVarInfo& fi = d_state.getFreeVarInfo(v);
    for (const Node& t : fi.d_useList)
    {
      d_state.notifyPatternSink(t);
      if (d_state.isFinished())
      {
        context()->pop();
        return false;
      }
    }
  }

  // now, all active quantified formulas that are still active should have
  // propagating instances.
  for (TNode q : slevel.d_finalQuants)
  {
    QuantInfo& qi = d_state.getQuantInfo(q);
    if (!qi.isActive())
    {
      continue;
    }
    // fully assigned and still active, can construct propagating instance
    // construct propagating instance
    const std::vector<TNode>& fvs = qi.getFreeVariables();
    Assert(q[0].getNumChildren() == fvs.size());
    std::vector<Node> inst;
    std::map<TNode, TNode> subs;
    for (size_t i = 0, nvars = fvs.size(); i < nvars; i++)
    {
      TNode vval = d_state.getGroundRepresentative(fvs[i]);
      if (vval.getKind() == BOUND_VARIABLE)
      {
        // unconstrained variable? take arbitrary ground term
        vval = vval.getType().mkGroundTerm();
      }
      inst.push_back(vval);
      subs[q[0][i]] = vval;
    }
    EntailmentCheck* ec = d_treg.getEntailmentCheck();
    Node instEval = ec->evaluateTerm(
        q[1], subs, false, options().quantifiers.qcfTConstraint, true);
    // If it is the case that instantiation can be rewritten to a Boolean
    // combination of terms that exist in the current context, then inst_eval
    // is non-null. Moreover, we insist that inst_eval is not true, or else
    // the instantiation is trivially entailed and hence is spurious.
    InferenceId id = InferenceId::QUANTIFIERS_INST_CCFV_PROP;
    if (instEval.isNull())
    {
      // ... spurious
      continue;
    }
    else if (instEval.isConst())
    {
      Assert(instEval.getType().isBoolean());
      if (instEval.getConst<bool>())
      {
        // ... spurious, entailed
        continue;
      }
      else
      {
        d_inConflict = true;
        id = InferenceId::QUANTIFIERS_INST_CCFV_CONFLICT;
      }
    }
    Instantiate* qinst = d_qim.getInstantiate();
    if (qinst->addInstantiation(q, inst, id))
    {
      d_foundInst = true;
    }
    else
    {
      // warning?
    }
  }

  return true;
}

void InstDriver::assignVar(TNode v, TNode eqc)
{
  Assert(d_qstate.getEqualityEngine()->consistent());
  Assert(!d_state.isSink(eqc));
  Assert(v.getType().isComparableTo(eqc.getType()));
  // assert to the equality engine
  Node eq = v.eqNode(eqc);
  d_keep.insert(eq);
  d_qstate.getEqualityEngine()->assertEquality(eq, true, eq);
  // should still be consistent
  Assert(d_qstate.getEqualityEngine()->consistent());
}

SearchLevel& InstDriver::getSearchLevel(size_t i) { return d_levels[i]; }

void InstDriver::search()
{
  Assert(!isFinished());
  bool isExhausted = false;
  size_t currLevel = 0;
  while (!isExhausted && !d_inConflict)
  {
    // assign at current level
    if (pushLevel(currLevel))
    {
      Assert(!isFinished());
      currLevel++;
    }
    else if (currLevel == 0)
    {
      isExhausted = true;
    }
    else
    {
      context()->pop();
      currLevel--;
    }
  }
}

bool InstDriver::isFinished() const
{
  return d_inConflict || d_state.isFinished();
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
