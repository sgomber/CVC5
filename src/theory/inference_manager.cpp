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

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

InferManager::InferManager(Theory& t, TheoryState& state)
    : d_theory(t),
      d_state(state),
      d_out(t.getOutputChannel()),
      d_ee(nullptr),
      d_pnm(nullptr)
{
}

void InferManager::setEqualityEngine(eq::EqualityEngine* ee) { d_ee = ee; }

void InferManager::conflictEqConstantMerge(TNode a, TNode b)
{
  if (!d_state.isInConflict())
  {
    TrustNode tconf = explainConflictEqConstantMerge(a, b);
    trustedConflict(tconf);
  }
}

void InferManager::conflict(TNode conf)
{
  if (!d_state.isInConflict())
  {
    d_out.conflict(conf);
  }
}

void InferManager::trustedConflict(TrustNode tconf)
{
  if (!d_state.isInConflict())
  {
    d_state.notifyInConflict();
    d_out.trustedConflict(tconf);
  }
}

bool InferManager::propagateLit(TNode lit)
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

TrustNode InferManager::explainLit(TNode lit)
{
  // TODO: use proof equality engine if it exists
  if (d_ee != nullptr)
  {
    Node exp = d_ee->mkExplainLit(lit);
    return TrustNode::mkTrustPropExp(lit, exp, nullptr);
  }
  Unimplemented() << "Inference manager for " << d_theory.getId()
                  << " was asked to explain a propagation but doesn't have an "
                     "equality engine or implement the "
                     "InferManager::explainLit interface!";
}

TrustNode InferManager::explainConflictEqConstantMerge(TNode a, TNode b)
{
  // TODO: use proof equality engine if it exists
  if (d_ee != nullptr)
  {
    Node lit = a.eqNode(b);
    Node conf = d_ee->mkExplainLit(lit);
    return TrustNode::mkTrustConflict(conf, nullptr);
  }
  Unimplemented() << "Inference manager for " << d_theory.getId()
                  << " mkTrustedConflictEqConstantMerge";
}

void InferManager::assertInternalFact(TNode atom, bool pol, TNode fact)
{
  if (d_theory.preNotifyFact(atom, pol, fact, false))
  {
    return;
  }
  Assert(d_ee != nullptr);
  Trace("infer-manager") << "InferManager::assertInternalFact: " << fact
                         << std::endl;
  if (atom.getKind() == kind::EQUAL)
  {
    d_ee->assertEquality(atom, pol, fact);
  }
  else
  {
    d_ee->assertPredicate(atom, pol, fact);
  }
  // call the notify fact method, where this is an internally generated fact
  d_theory.notifyFact(atom, pol, fact, true);
  Trace("infer-manager") << "InferManager::finished assertInternalFact"
                         << std::endl;
  // TODO: keep set for fact?
}

}  // namespace theory
}  // namespace CVC4
