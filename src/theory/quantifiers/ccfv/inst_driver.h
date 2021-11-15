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

#include "theory/quantifiers/ccfv/state.h"
#include "smt/env_obj.h"

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

 private:
  /** are we finished? */
  bool isFinished() const;
  TNode getNextVariable();
  /**
   * Push variable v to the stack.
   */
  void pushVar(TNode v);
  void popVar();

  void assignVar(TNode v, TNode eqc);

  /** The state of matching for quantifiers and pattern terms */
  State& d_state;
  /** Reference to the state of the quantifiers engine */
  QuantifiersState& d_qstate;
  /** Reference to the term registry */
  TermRegistry& d_treg;

  /** The current stack of quantified variables */
  std::vector<TNode> d_varStack;

  /** The set of quantified formulas */
  //QuantifiersSet d_qset;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
