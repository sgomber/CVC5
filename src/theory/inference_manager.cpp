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

InferenceManager::InferenceManager(TheoryId tid,
                                   TheoryState& state,
                                   OutputChannel& out,
                                   ProofNodeManager* pnm)
    : d_theoryId(tid), d_state(state), d_out(out), d_ee(nullptr), d_pnm(pnm)
{
}

void InferenceManager::setEqualityEngine(eq::EqualityEngine* ee) { d_ee = ee; }

void InferenceManager::conflictEqConstantMerge(TNode a, TNode b)
{
  if (!d_state.isInConflict())
  {
    TrustNode tconf = mkTrustedConflictEqConstantMerge(a, b);
    trustedConflict(tconf);
  }
}

void InferenceManager::conflict(TNode conf)
{
  if (!d_state.isInConflict())
  {
    TrustNode tconf = mkTrustedConflict(conf);
    trustedConflict(tconf);
  }
}

void InferenceManager::trustedConflict(TrustNode tconf)
{
  if (!d_state.isInConflict())
  {
    d_state.notifyInConflict();
    d_out.trustedConflict(tconf);
  }
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

TrustNode InferenceManager::explain(TNode n)
{
  // TODO
  Unimplemented() << "Theory " << d_theoryId
                  << " sent a conflict but doesn't implement the "
                     "Theory::explain() interface!";
}

TrustNode InferenceManager::mkTrustedConflictEqConstantMerge(TNode a, TNode b)
{
  // TODO
  Unimplemented() << "Theory " << d_theoryId
                  << " mkTrustedConflictEqConstantMerge";
}

TrustNode InferenceManager::mkTrustedConflict(TNode conf)
{
  // TODO
  Unimplemented() << "Theory " << d_theoryId << " mkTrustedConflict";
}

}  // namespace theory
}  // namespace CVC4
