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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__INST_DRIVER_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__INST_DRIVER_H

#include "smt/env_obj.h"
#include "theory/quantifiers/ccfv/matching.h"
#include "theory/quantifiers/ccfv/search_level.h"
#include "theory/quantifiers/ccfv/state.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;
class QuantifiersInferenceManager;
class TermRegistry;

namespace ccfv {

/**


Q1: x : T1, y : T2
Q2: y : T2, w : T2

--- Q1
x -> a
  --- Q2
  y -> b
    w -> c
    w -> d
  y -> c
    w -> d
  y -> d
  y -> e
x -> b
  y -> b
  y -> e
  y -> f

// maybe process when none instead of when firstTime?
Q1 xyz
Q2 z
Q3 xw
Q4 zu
Q5 wv

d_varsToAssign / d_finalQuant / d_startQuant
1: x  {}  /  {Q5}
2: yw {Q3}  / {Q2, Q4}
3: zv {Q1, Q2, Q5} / {}
4: u  {Q4} / {}


*/
class InstDriver : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  InstDriver(Env& env,
             State& state,
             QuantifiersState& qs,
             QuantifiersInferenceManager& qim,
             TermRegistry& tr);
  /** check */
  void check(const std::vector<TNode>& quants);
  /** Are we in conflict? */
  bool inConflict() const;
  /** The number of instantiations added */
  size_t numFoundInst() const;

 private:
  /** Reset the search */
  void resetSearchLevels(const std::vector<TNode>& quants);
  /** Assign variable levels for all quantifiers */
  void assignVarsToLevels(size_t level,
                          const std::vector<TNode>& quants,
                          std::map<TNode, std::vector<TNode>>& partition,
                          std::map<TNode, size_t>& fvLevel);
  /** Initialize at level */
  void initializeLevel(size_t level);
  /** End level */
  void endLevel(size_t level);
  /** Assign search level */
  bool pushLevel(size_t level);
  /** Add to equality engine */
  void addToEqualityEngine(QuantInfo& qi);
  /** Assign variable to the equivalence class eqc */
  void assignVar(TNode v, TNode eqc);
  /** Get search level */
  SearchLevel& getSearchLevel(size_t i);
  /** Search */
  void search();
  /** Is finished */
  bool isFinished() const;
  /** The state of matching for quantifiers and pattern terms */
  State& d_state;
  /** Reference to the state of the quantifiers engine */
  QuantifiersState& d_qstate;
  /** Reference to the quantifiers inference manager */
  QuantifiersInferenceManager& d_qim;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  /** Matching utility */
  Matching d_matching;
  /** Search levels */
  std::map<size_t, SearchLevel> d_levels;
  /** Number of levels */
  size_t d_numLevels;
  /** Have we found any instance? */
  size_t d_foundInst;
  /** mapping to instances */
  std::map<TNode, std::vector<std::vector<Node>>> d_insts;
  /** Index of conflicting instances (for debugging) */
  std::map<TNode, std::unordered_set<size_t>> d_conflictInstIndex;
  /** Have we found a conflicting instance? */
  bool d_inConflict;
  /** Quantified formulas that are out of scope */
  std::vector<Node> d_noScopeQuant;
  /** The index in the above vector that we have processed */
  context::CDO<size_t> d_noScopeQuantIndex;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
