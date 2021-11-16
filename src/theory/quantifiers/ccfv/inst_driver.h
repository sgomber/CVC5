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
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__INST_DRIVER_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__INST_DRIVER_H

#include "smt/env_obj.h"
#include "theory/quantifiers/ccfv/search_level.h"
#include "theory/quantifiers/ccfv/state.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

class QuantifiersState;
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

*/
class InstDriver : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;
 public:
  InstDriver(Env& env, State& state, QuantifiersState& qs, TermRegistry& tr);
  /** Get quantifiers info */
  QuantInfo& getQuantInfo(TNode q);
  /** Get free variable info */
  FreeVarInfo& getFreeVarInfo(TNode v);
  /** Get pattern term info */
  PatTermInfo& getPatTermInfo(TNode p);
  /** Get equivalence class info */
  EqcInfo& getEqcInfo(TNode r);

  /** check */
  void check(const std::vector<TNode>& quants);

 private:
  /** Reset the search */
  void resetSearchLevels(const std::vector<TNode>& quants);
  /** Assign variable levels for all quantifiers */
  void assignVarsToLevels(size_t level,
                          const std::vector<TNode>& quants,
                          std::map<TNode, std::vector<TNode>>& partition,
                          std::map<TNode, size_t>& fvLevel);
  /** Assign search level */
  bool pushLevel(size_t level);
  /** Assign variable to the equivalence class eqc */
  void assignVar(TNode v, TNode eqc);
  /** Process matcher */
  bool processMatcher(QuantInfo& qi, TNode matcher);
  /** Run matching */
  void runMatching(PatTermInfo* pi);
  /** Get search level */
  SearchLevel& getSearchLevel(size_t i);
  /** Search */
  void search();
  /** common constants */
  Node d_true;
  Node d_false;
  /** The state of matching for quantifiers and pattern terms */
  State& d_state;
  /** Reference to the state of the quantifiers engine */
  QuantifiersState& d_qstate;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  /** Search levels */
  std::map<size_t, SearchLevel> d_levels;
  /** Number of levels */
  size_t d_numLevels;
  /** Keep set, for asserted equalities */
  NodeSet d_keep;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
