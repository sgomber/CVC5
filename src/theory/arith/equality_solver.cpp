/*********************                                                        */
/*! \file equality_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arithmetic equality solver.
 **/

#include "theory/arith/equality_solver.h"

#include "theory/arith/theory_arith.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

EqualitySolver::EqualitySolver(ArithState& astate, InferManager& aim)
    : d_astate(astate),
      d_aim(aim),
      d_notify(*this, aim),
      d_ee(nullptr),
      d_propLits(astate.getSatContext())
{
}

bool EqualitySolver::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::arith::EqualitySolver";
  return true;
}

void EqualitySolver::setEqualityEngine(eq::EqualityEngine* ee) { d_ee = ee; }

bool EqualitySolver::preNotifyFact(TNode atom, bool pol, TNode fact)
{
  return atom.getKind() != EQUAL;
}

TrustNode EqualitySolver::explainLit(TNode lit)
{
  // if we propagated this, we explain it
  if (d_propLits.find(lit) != d_propLits.end())
  {
    return d_aim.explainLit(lit);
  }
  return TrustNode::null();
}

bool EqualitySolver::propagateLit(TNode lit)
{
  Assert(d_propLits.find(lit) == d_propLits.end());
  d_propLits.insert(lit);
  return d_aim.propagateLit(lit);
}

void EqualitySolver::notifyFact(TNode atom,
                                bool pol,
                                TNode fact,
                                bool isInternal)
{
  // do nothing for now, but we could be more aggressive
}

bool EqualitySolver::EqualitySolverNotify::eqNotifyTriggerPredicate(
    TNode predicate, bool value)
{
  if (value)
  {
    return d_esolver.propagateLit(predicate);
  }
  return d_esolver.propagateLit(predicate.notNode());
}

bool EqualitySolver::EqualitySolverNotify::eqNotifyTriggerTermEquality(
    TheoryId tag, TNode t1, TNode t2, bool value)
{
  if (value)
  {
    return d_esolver.propagateLit(t1.eqNode(t2));
  }
  return d_esolver.propagateLit(t1.eqNode(t2).notNode());
}

void EqualitySolver::EqualitySolverNotify::eqNotifyConstantTermMerge(TNode t1,
                                                                     TNode t2)
{
  return d_aim.conflictEqConstantMerge(t1, t2);
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
