/*********************                                                        */
/*! \file inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An inference manager for Theory
 **/

#include "theory/inference_manager.h"

#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {

InferenceManager::InferenceManager(TheoryState& state, OutputChannel& out) : d_state(state), d_out(out), d_ee(nullptr) {}

void InferenceManager::setEqualityEngine(eq::EqualityEngine* ee)
{
}

void InferenceManager::conflictConstantEq(TNode a, TNode b)
{
}

void InferenceManager::conflict(TNode conf)
{
}

void InferenceManager::trustedConflict(TrustNode tconf)
{
}

bool InferenceManager::propagate(TNode lit)
{
  // If already in conflict, no more propagation
  if (d_state.isInConflict())
  {
    return false;
  }
  // Propagate out
  bool ok = d_out.propagate(lit);
  if (!ok)
  {
    d_state.notifyInConflict();
  }
  return ok;
}


}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__INFERENCE_MANAGER_H */
