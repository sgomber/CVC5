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
 * Runs global matching.
 *
 * This class does matching modulo equality for terms. It does not generate
 * substitutions, instead its main purpose is to set a relevant domain of
 * variables.
 *
 * For example, say our E-graph is
 *   { a, f(a,b,c), f(c,c,d), g(c), g(d) } { b, c }, { e }, { d }
 * where the first term in each equivalence class is the representative.
 *
 * Each pattern has a set of unprocessed and processed "watched equivalence
 * classes" W. Assume initially that:
 *   W(f(g(x),y,b)) = {a} / {}
 * Running matching on this term will match f(g(x),e) against f-applications
 * in the equivalence class of a and updates W:
 *   W(f(g(x),y,b)) = {} / {a}
 *   W(g(x)) = {a} / {}
 *   W(y) = {b} / {}
 * Notice that f(g(x),y,b) does not match f(c,c,d) since E |/= (b = d), so it
 * does not add to W. We match for g(x) recursively:
 *   W(f(g(x),y,b)) = {} / {a}
 *   W(g(x)) = {} / {a}
 *   W(y) = {b} / {}
 *   W(x) = {c, d} / {}
 * Notice that matching does not process the watched equivalence classes of
 * variables.
 *
 * As a result, substitutions x -> {c, d}, y -> {b} are relevant for making
 * f(g(x),y,b) equal to a.
 */
class Matching : protected EnvObj
{
 public:
  Matching(Env& env, State& state, QuantifiersState& qs);
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
