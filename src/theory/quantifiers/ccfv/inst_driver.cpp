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
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/uf/equality_engine.h"
#include "options/quantifiers_options.h"

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
      d_numLevels(0),
      d_keep(context()),
      d_inConflict(false)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

void InstDriver::check(const std::vector<TNode>& quants)
{
  d_inConflict = false;
  // reset round for all quantified formulas
  for (TNode q : quants)
  {
    QuantInfo& qi = d_state.getQuantInfo(q);
    qi.resetRound();
  }
  // reset search levels
  // NOTE: could incrementally maintain this?
  resetSearchLevels(quants);

  // now perform the search
  search();
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
    Assert (q[0].getNumChildren()==fvs.size());
    std::vector<Node> inst;
    std::map<TNode, TNode> subs;
    for (size_t i=0, nvars = fvs.size(); i<nvars; i++)
    {
      TNode vval = d_state.getGroundRepresentative(fvs[i]);
      if (vval.getKind()==BOUND_VARIABLE)
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
      Assert (instEval.getType().isBoolean());
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
    if (!qinst->addInstantiation(q, inst, id))
    {
      
    }
  }

  return true;
}

bool InstDriver::processMatcher(QuantInfo& qi, TNode matcher)
{
  PatTermInfo& pi = d_state.getPatTermInfo(matcher);
  if (!pi.isActive())
  {
    return false;
  }
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
  runMatching(&pi);
  return true;
}

void InstDriver::runMatching(PatTermInfo* pi)
{
  Assert(pi != nullptr);
  TNode op = pi->d_matchOp;
  if (op.isNull())
  {
    // If not a matchable operator. This is also the base case of
    // BOUND_VARIABLE.
    return;
  }  
  TNode weqc = pi->getNextWatchEqc();
  if (weqc.isNull())
  {
    // no new equivalence classes to process
    return;
  }
  std::vector<TNode> pargs;
  std::vector<PatTermInfo*> piargs;
  std::vector<size_t> matchIndices;
  std::vector<size_t> nmatchIndices;
  std::unordered_map<TNode, std::vector<Node>>::iterator itm;
  while (!weqc.isNull())
  {
    Assert(d_state.isGroundEqc(weqc));
    MatchEqcInfo& meqc = d_state.getMatchEqcInfo(weqc);

    // get the terms to match in this equivalence class
    itm = meqc.d_matchOps.find(op);
    if (itm == meqc.d_matchOps.end())
    {
      // no matchable terms in this equivalence class
    }
    else
    {
      // set up the matching information for pi->d_pattern
      if (pargs.empty())
      {
        // get the status of the arguments of pi
        Assert(pi->d_pattern.getNumChildren() > 0);
        for (size_t i = 0, nchild = pi->d_pattern.getNumChildren(); i < nchild; i++)
        {
          TNode pic = pi->d_pattern[i];
          // Note we use get ground representative here. We do not use getValue,
          // which should never be sink.
          TNode gpic = d_state.getGroundRepresentative(pic);
          pargs.push_back(gpic);
          if (!gpic.isNull())
          {
            matchIndices.push_back(i);
            piargs.push_back(nullptr);
          }
          else
          {
            nmatchIndices.push_back(i);
            piargs.push_back(&d_state.getPatTermInfo(pic));
          }
        }
        // we should not have ground representatives for each child of the pattern,
        // otherwise we should be fully assigned
        Assert(!nmatchIndices.empty());
      }
      // none in this equivalence class
      // for each term with the same match operator
      bool isMaybeEq = false;
      for (const Node& m : itm->second)
      {
        Assert(m.getNumChildren() == pargs.size());
        bool matchSuccess = true;
        for (size_t i : matchIndices)
        {
          Assert(d_state.isGroundEqc(m[i]));
          if (pargs[i] != m[i])
          {
            matchSuccess = false;
            break;
          }
        }
        // if successful, we will match the children of this pattern to the
        // ground equivalence class
        if (matchSuccess)
        {
          for (size_t i : nmatchIndices)
          {
            piargs[i]->addWatchEqc(m[i]);
            // recurse to do matching on the argument
            runMatching(piargs[i]);
            // if it is not possible that we are equal, we stop matching this
            // term
            if (!piargs[i]->isMaybeEqc(m[i]))
            {
              matchSuccess = false;
              break;
            }
          }
          isMaybeEq = isMaybeEq || matchSuccess;
        }
      }
      // if its possible that we are equal by matching, record this here
      if (isMaybeEq)
      {
        pi->addMaybeEqc(weqc);
      }
    }
    // increment weqc to the next equivalence class
    weqc = pi->getNextWatchEqc();
  }
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
  context()->push();
  // TODO: do initial notifications for watched ground terms
  
  if (isFinished())
  {
    return;
  }
  
  bool isExhausted = false;
  size_t currLevel = 0;
  while (!isExhausted)
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
  
  context()->pop();
}

bool InstDriver::isFinished() const
{
  return d_inConflict || d_state.isFinished();
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
