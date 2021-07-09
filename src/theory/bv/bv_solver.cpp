/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bit-vector solver interface.
 *
 * Describes the interface for the internal bit-vector solver of TheoryBV.
 */

#include "theory/bv/bv_solver.h"

#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"

namespace cvc5 {
namespace theory {
namespace bv {

BVSolver::BVSolver(TheoryState& state, TheoryInferenceManager& inferMgr)
    : d_state(state), d_im(inferMgr){}

EqualityStatus BVSolver::getEqualityStatus(TNode a, TNode b)
{
  eq::EqualityEngine * ee = d_state.getEqualityEngine();
  if (ee!=nullptr)
  {
    Assert(ee->hasTerm(a) && ee->hasTerm(b));

    // Check for equality (simplest)
    if (ee->areEqual(a, b))
    {
      // The terms are implied to be equal
      return EQUALITY_TRUE;
    }

    // Check for disequality
    if (ee->areDisequal(a, b, false))
    {
      // The terms are implied to be dis-equal
      return EQUALITY_FALSE;
    }
  }
  return EqualityStatus::EQUALITY_UNKNOWN;
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5

