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

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__MATCHING_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__MATCHING_H

#include "smt/env_obj.h"
#include "theory/quantifiers/ccfv/state.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

class QuantifiersState;
class QuantifiersInferenceManager;
class TermRegistry;

namespace ccfv {

/**
*/
class Matching : protected EnvObj
{
 public:
  Matching(Env& env,
             State& state,
             QuantifiersState& qs);
  /** Process matcher */
  bool processMatcher(QuantInfo& qi, TNode matcher);
private:
  /** Run matching */
  void runMatching(PatTermInfo* pi);
  /** common constants */
  Node d_true;
  Node d_false;
  /** The state of matching for quantifiers and pattern terms */
  State& d_state;
  /** Reference to the state of the quantifiers engine */
  QuantifiersState& d_qstate;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
