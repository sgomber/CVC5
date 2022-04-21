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
 * Search procedure for instantiations in CCFV
 */

#include "theory/quantifiers/ccfv/inst_driver.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/uf/equality_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
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
      d_matching(env, state, qs, tr.getTermDatabase()),
      d_numLevels(0),
      d_foundInst(0),
      d_inConflict(false),
      d_noScopeQuantIndex(context(), 0)
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

  Trace("ccfv-debug") << "Reset " << quants.size() << " quants..." << std::endl;
  TermDb* tdb = d_treg.getTermDatabase();
  std::vector<TNode> activeQuants;
  for (TNode q : quants)
  {
    QuantInfo& qi = d_state.getQuantInfo(q);
    qi.resetRound(tdb);
    if (qi.isActive())
    {
      activeQuants.push_back(q);
    }
  }
  Trace("ccfv-debug") << "..." << activeQuants.size() << "/" << quants.size()
                      << " are initially active" << std::endl;

  if (activeQuants.empty())
  {
    return;
  }

  // we modify the equality engine, so we push the SAT context
  int prevLevel = context()->getLevel();
  context()->push();

  // reset information about whether we have found instantiations
  d_foundInst = 0;
  d_insts.clear();
  d_conflictInstIndex.clear();
  d_inConflict = false;
  d_noScopeQuant.clear();
  d_noScopeQuantIndex = 0;

  Trace("ccfv-debug") << "Add quant bodies to equality engine..." << std::endl;
  for (TNode q : activeQuants)
  {
    QuantInfo& qi = d_state.getQuantInfo(q);
    // add congruence terms from quantified formulas to the equality engine
    addToEqualityEngine(qi);
  }

  // Reset the state. Notice that we must do this *after* adding pattern terms
  // to the equality engine, since ground terms in quantifier bodies should
  // be considered "known" terms.
  Trace("ccfv-debug") << "Reset state..." << std::endl;
  d_state.resetRound(activeQuants.size());

  // do initial notifications for relevant ground terms in the bodies of
  // quantified formulas.
  FreeVarInfo& fiNull = d_state.getOrMkFreeVarInfo(Node::null());
  Trace("ccfv-debug") << "Initial notify " << fiNull.d_finalTerms.size()
                      << " ground terms..." << std::endl;
  for (const Node& t : fiNull.d_finalTerms)
  {
    TNode trep = d_state.getGroundRepresentative(t);
    if (trep.isNull())
    {
      d_state.notifyPatternNone(t);
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
    resetSearchLevels(activeQuants);
    Trace("ccfv-debug") << "Search..." << std::endl;
    Trace("ccfv-debug") << d_state.toString() << std::endl;
    search();
    Trace("ccfv-debug") << "...finished" << std::endl;
  }
  else
  {
    Trace("ccfv-debug") << "...already finished" << std::endl;
  }

  // pop the context that was done at the beginning
  context()->pop();
  AlwaysAssert(context()->getLevel() == prevLevel)
      << "Context mismatch: " << prevLevel << " != " << context()->getLevel();

  // Now send instantiations. We do this only after popping the scope
  Instantiate* qinst = d_qim.getInstantiate();
  for (std::pair<const TNode, std::vector<std::vector<Node>>>& i : d_insts)
  {
    Node q = i.first;
    std::unordered_set<size_t>& cci = d_conflictInstIndex[q];
    for (size_t ii = 0, ninst = i.second.size(); ii < ninst; ii++)
    {
      InferenceId id = cci.find(ii) != cci.end()
                           ? InferenceId::QUANTIFIERS_INST_CCFV_CONFLICT
                           : InferenceId::QUANTIFIERS_INST_CCFV_PROP;
      if (qinst->addInstantiation(q, i.second[ii], id))
      {
        Trace("ccfv-inst") << "Added instance for " << q.getId() << " : "
                           << i.second[ii] << std::endl;
      }
      else if (id == InferenceId::QUANTIFIERS_INST_CCFV_CONFLICT)
      {
        Trace("ccfv-inst") << "FAILED to add instance for " << q.getId()
                           << " : " << i.second[ii] << std::endl;
        Trace("ccfv-warn") << "Failed to add instantiation " << i.second[ii]
                           << " for " << q << std::endl;
        AlwaysAssert(false)
            << "Failed CCFV instantiation: " << i.second[ii] << " for " << q;
      }
      else
      {
        // propagating instances may be entailed
      }
    }
  }
}

bool InstDriver::inConflict() const { return d_inConflict; }

size_t InstDriver::numFoundInst() const { return d_foundInst; }

void InstDriver::resetSearchLevels(const std::vector<TNode>& quants)
{
  // compute the levels at which the variables are at
  d_levels.clear();
  std::map<TNode, std::vector<TNode>> partition;
  std::map<TNode, size_t> fvLevel;
  assignVarsToLevels(0, quants, partition, fvLevel);
  d_numLevels = d_levels.size();

  // set the start levels
  std::map<TNode, size_t>::iterator itf;
  for (TNode q : quants)
  {
    QuantInfo& qi = d_state.getQuantInfo(q);
    const std::vector<TNode>& fvs = qi.getOrderedFreeVariables();
    Assert(!fvs.empty());
    itf = fvLevel.find(fvs[0]);
    Assert(itf != fvLevel.end());
    // don't need to set quantified formulas at level 0, these have no impact
    if (itf->second > 0)
    {
      SearchLevel& slevel = getSearchLevel(itf->second);
      slevel.d_startQuants.push_back(q);
    }
  }
  // set that it is the first time seeing each of the levels
  for (std::pair<const size_t, SearchLevel>& sl : d_levels)
  {
    Assert(sl.first < d_numLevels);
    sl.second.d_firstTimePre = true;
    sl.second.d_firstTimePost = true;
  }

  if (TraceIsOn("ccfv-search-levels"))
  {
    for (std::pair<const size_t, SearchLevel>& sl : d_levels)
    {
      Trace("ccfv-search-levels")
          << "Search level #" << sl.first << ":" << std::endl;
      Trace("ccfv-search-levels") << sl.second.toStringDebug() << std::endl;
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
  SearchLevel* slevel = level == 0 ? nullptr : &getSearchLevel(level - 1);
  // every next variable must be included in this subtree
  std::vector<TNode> nextVars;
  // for each quantified formula that we require assigning next variable
  for (TNode q : quants)
  {
    QuantInfo& qi = d_state.getQuantInfo(q);
    TNode next = qi.getNextSearchVariable();
    if (next.isNull())
    {
      Assert(slevel != nullptr);
      // fully assigned at this level
      slevel->d_finalQuants.push_back(q);
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
  if (nextVars.empty())
  {
    return;
  }
  // Add each variable to the search, which may make recursive calls that
  // process the variables lower. Those that are not processed in lower levels
  // are processed here.
  slevel = &getSearchLevel(level);
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
      slevel->d_varsToAssign.push_back(v);
      fvLevel[v] = level;
      nextLevel = level + 1;
    }
    assignVarsToLevels(nextLevel, nextQuants, partition, fvLevel);
  }
}

void InstDriver::initializeLevel(size_t level)
{
  d_matching.initializeLevel(level);
  // reset counter for quantified formulas
  SearchLevel& slevel = getSearchLevel(level);
  for (TNode v : slevel.d_varsToAssign)
  {
    FreeVarInfo& fi = d_state.getFreeVarInfo(v);
    fi.resetLevel();
  }
  if (TraceIsOn("ccfv-search-debug"))
  {
    Trace("ccfv-search-debug") << d_state.toStringDebugSearch() << std::endl;
  }
}

void InstDriver::endLevel(size_t level)
{
  // activate quantified formulas that are first time
  SearchLevel& slevel = getSearchLevel(level);
  if (slevel.d_firstTimePost)
  {
    d_noScopeQuant.insert(d_noScopeQuant.end(),
                          slevel.d_startQuants.begin(),
                          slevel.d_startQuants.end());
    slevel.d_firstTimePost = false;
  }
  // referesh set all the out of scope quantified formulas to inactive
  while (d_noScopeQuantIndex.get() < d_noScopeQuant.size())
  {
    TNode nsq = d_noScopeQuant[d_noScopeQuantIndex.get()];
    QuantInfo& qi = d_state.getQuantInfo(nsq);
    d_state.setQuantInactive(qi);
    d_noScopeQuantIndex = d_noScopeQuantIndex.get() + 1;
  }
}

bool InstDriver::pushLevel(size_t level)
{
  if (isFinished())
  {
    // already finished
    return false;
  }
  SearchLevel& slevel = getSearchLevel(level);
  bool wasFirstTimePre = slevel.d_firstTimePre;
  slevel.d_firstTimePre = false;
  Assert(!slevel.d_varsToAssign.empty());
  // Find the next assignment for each variable. Variables that are at the
  // same level can be assigned in parallel.
  std::vector<TNode> assignment;
  bool success = false;
  std::map<TNode, MatchPatInfo>& mpm = d_matching.getMatchPatInfo(level);
  // assign all variables in parallel
  for (TNode v : slevel.d_varsToAssign)
  {
    Trace("ccfv-matching") << "  process matching for " << v << std::endl;
    MatchPatInfo& mpi = mpm[v];
    FreeVarInfo& fi = d_state.getFreeVarInfo(v);
    TNode eqc = mpi.getNextWatchEqc();
    while (eqc.isNull())
    {
      // get the next quantified formula containing v
      TNode q = fi.getNextQuantifier();
      if (q.isNull())
      {
        // no more quantifiers to match
        Trace("ccfv-matching") << "  ...no quantifiers" << std::endl;
        break;
      }
      QuantInfo& qi = d_state.getQuantInfo(q);
      if (!qi.isActive())
      {
        // quantified formula is not active
        continue;
      }
      TNode matcher = qi.getMatcherFor(v);
      Trace("ccfv-matching")
          << "  ...matcher " << matcher << " from " << q.getId() << std::endl;
      if (matcher.isNull())
      {
        // doesn't have a matcher for this variable, continue
        continue;
      }
      if (!d_matching.processMatcher(level, qi, matcher))
      {
        // failed to process matcher, e.g. a top-level constraint was
        // not satisfied
        continue;
      }
      // maybe succeeded match?
      eqc = mpi.getNextWatchEqc();
    }
    Trace("ccfv-matching") << "  ...return watched " << eqc << std::endl;
    if (eqc.isNull())
    {
      eqc = d_state.getNone();
    }
    else
    {
      success = true;
    }
    assignment.push_back(eqc);
  }
  if (!success && !wasFirstTimePre)
  {
    // Could not find an assignment to any variables, and we already ran
    // the level below this one. In this case, a previous assignment ran
    // strictly more information.
    Trace("ccfv-search") << "...no assignment" << std::endl;
    return false;
  }
  // we push here, since we are updating the state of the equality engine

  context()->push();
  // assign each variable
  if (TraceIsOn("ccfv-search"))
  {
    Trace("ccfv-search") << "assign:";
    for (size_t i = 0, nvars = slevel.d_varsToAssign.size(); i < nvars; i++)
    {
      TNode v = slevel.d_varsToAssign[i];
      TNode eqc = assignment[i];
      Trace("ccfv-search") << " " << v << " -> " << eqc;
    }
    Trace("ccfv-search") << std::endl;
  }
  for (size_t i = 0, nvars = slevel.d_varsToAssign.size(); i < nvars; i++)
  {
    TNode v = slevel.d_varsToAssign[i];
    TNode eqc = assignment[i];
    const FreeVarInfo& fi = d_state.getFreeVarInfo(v);
    if (d_state.isNone(eqc))
    {
      d_state.notifyPatternNone(v);
      // Disable all quantified formulas that contain this variable? NOTE: this
      // may be redundant, as quantified formulas that have a variable assigned
      // to none should likely be set inactive for other reasons.
      for (const Node& q : fi.d_quantList)
      {
        QuantInfo& qi = d_state.getQuantInfo(q);
        if (qi.isActive())
        {
          d_state.setQuantInactive(qi);
          if (d_state.isFinished())
          {
            Trace("ccfv-search")
                << "...finished while setting quant inactive" << std::endl;
            return true;
          }
        }
      }
    }
    else
    {
      // otherwise, assert v = eqc to the equality engine
      d_state.assertEquality(v, eqc);
    }
    if (d_state.isFinished())
    {
      Trace("ccfv-search") << "...finished after assignment" << std::endl;
      return true;
    }
    if (TraceIsOn("ccfv-matching-debug"))
    {
      Trace("ccfv-matching-debug") << "E-graph after assignment:" << std::endl;
      Trace("ccfv-matching-debug")
          << d_qstate.getEqualityEngine()->debugPrintEqc() << std::endl;
    }
    Trace("ccfv-search-debug") << "Process final terms for " << v << std::endl;
    // assign final terms to none
    // The use list terms of the variables to assign here are those that are now
    // fully assigned. If these terms have not yet merged, we are done.
    for (const Node& t : fi.d_finalTerms)
    {
      Trace("ccfv-search-debug") << "...final: " << t << std::endl;
      d_state.notifyPatternNone(t);
      if (d_state.isFinished())
      {
        Trace("ccfv-search")
            << "...finished while setting term inactive" << std::endl;
        return true;
      }
    }
  }

  // now, all active quantified formulas that are still active should have
  // propagating instances.
  Trace("ccfv-search-debug") << "Process final quants" << std::endl;
  NodeManager * nm = NodeManager::currentNM();
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
    for (size_t i = 0, nvars = fvs.size(); i < nvars; i++)
    {
      TNode vval = d_state.getGroundRepresentative(fvs[i]);
      if (vval.getKind() == BOUND_VARIABLE)
      {
        // unconstrained variable? take arbitrary ground term
        vval = nm->mkGroundTerm(vval.getType());
      }
      inst.push_back(vval);
    }
    Trace("ccfv-search") << "...instantiation for " << q.getId() << " : "
                         << inst << std::endl;
    if (qi.isMaybeConflict())
    {
      d_inConflict = true;
      d_conflictInstIndex[q].insert(d_insts[q].size());
      Trace("ccfv-search") << "...conflict!" << std::endl;
    }
    else
    {
      Trace("ccfv-search") << "...propagating!" << std::endl;
    }
    d_insts[q].emplace_back(inst);
    // now, set the quantified formula inactive
    d_state.setQuantInactive(qi);
    if (d_state.isFinished())
    {
      Trace("ccfv-search") << "...finished after processing inst" << std::endl;
      return true;
    }
  }
  Trace("ccfv-search") << "...successful assign" << std::endl;
  return true;
}

SearchLevel& InstDriver::getSearchLevel(size_t i) { return d_levels[i]; }

void InstDriver::search()
{
  Assert(!isFinished());
  Assert(d_numLevels > 0);
  Trace("ccfv-search") << "search: start" << std::endl;
  bool isExhausted = false;
  size_t currLevel = 0;
  initializeLevel(0);
  while (!isExhausted && !d_inConflict)
  {
    Assert(currLevel < d_numLevels);
    Trace("ccfv-search") << "search: level = " << currLevel << ", "
                         << d_state.toStringSearch() << std::endl;
    // assign all variables at current level, this returns true if the
    // context was pushed, false otherwise.
    if (pushLevel(currLevel))
    {
      if (!isFinished() && currLevel + 1 < d_numLevels)
      {
        currLevel++;
        initializeLevel(currLevel);
      }
      else
      {
        // we may be finished after the last assignment, or we may have hit the
        // maximum levels, in this case, we pop the context and try the next
        // assignment at the current level.
        context()->pop();
      }
    }
    else if (currLevel == 0)
    {
      isExhausted = true;
    }
    else
    {
      context()->pop();
      endLevel(currLevel);
      currLevel--;
    }
  }
  // if we terminated early, process any necessary context pops
  while (currLevel > 0)
  {
    context()->pop();
    currLevel--;
  }
  Trace("ccfv-search") << "search: finished, conflict = " << d_inConflict
                       << std::endl;
}

bool InstDriver::isFinished() const
{
  return d_inConflict || d_state.isFinished();
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
