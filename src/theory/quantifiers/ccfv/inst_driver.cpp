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
}

void InstDriver::check(const std::vector<TNode>& quants)
{
  // reset round for all quantified formulas
  for (TNode q : quants)
  {
    QuantInfo& qi = d_state.getQuantInfo(q);
    qi.resetRound();
  }
  // reset information for quantified formulas
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

bool InstDriver::isFinished() const { return d_state.isFinished(); }

void InstDriver::assignVar(TNode v, TNode eqc)
{
  Assert(d_qstate.getEqualityEngine()->consistent());
  // assert to the equality engine
  Node eq = v.eqNode(eqc);
  d_qstate.getEqualityEngine()->assertEquality(eq, true, eq);
  // should still be consistent
  Assert(d_qstate.getEqualityEngine()->consistent());
}

SearchLevel& InstDriver::getSearchLevel(size_t i) { return d_levels[i]; }

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
