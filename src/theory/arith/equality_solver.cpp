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

void EqualitySolver::setEqualityEngine(eq::EqualityEngine* ee)
{
  d_ee = ee;
  // add the function kinds
  d_ee->addFunctionKind(kind::NONLINEAR_MULT);
  d_ee->addFunctionKind(kind::EXPONENTIAL);
  d_ee->addFunctionKind(kind::SINE);
  d_ee->addFunctionKind(kind::IAND);
}

bool EqualitySolver::preNotifyFact(TNode atom, bool pol, TNode fact)
{
  if (atom.getKind() == EQUAL)
  {
    Trace("arith-eq-solver")
        << "EqualitySolver::preNotifyFact: " << fact << std::endl;
    Trace("arith-eq-solver")
        << "(in state " << d_astate.toString() << ")" << std::endl;
    // we will process
    return false;
  }
  // don't process
  return true;
}

TrustNode EqualitySolver::explainLit(TNode lit)
{
  // if we propagated this, we explain it
  NodeMap::const_iterator it = d_propLits.find(lit);
  if (it != d_propLits.end() && (*it).second)
  {
    Trace("arith-eq-solver")
        << "EqualitySolver::explainLit: " << d_astate.toString() << std::endl;
    TrustNode texp = d_aim.explainLit(lit);

    Trace("arith-eq-solver") << "EqualitySolver::explainLit: " << lit
                             << " returned " << texp.getNode() << std::endl;
    return texp;
  }
  return TrustNode::null();
}

bool EqualitySolver::propagateLit(TNode lit)
{
#if 0
  return d_aim.propagateManagedLit(lit, false);
#endif
  if (hasPropagated(lit))
  {
    // already propagated
    return true;
  }
  Trace("arith-eq-solver") << "EqualitySolver::propagateLit: " << lit << " in "
                           << d_astate.toString() << std::endl;
  d_propLits[lit] = true;
  bool ret = d_aim.propagateLit(lit);
  Trace("arith-eq-solver") << "...return " << ret << ", state is now "
                           << d_astate.toString() << std::endl;
  return ret;
}

bool EqualitySolver::hasPropagated(TNode lit) const
{
  return d_propLits.find(lit) != d_propLits.end();
}

void EqualitySolver::notifyPropagated(TNode lit) { d_propLits[lit] = false; }

void EqualitySolver::notifyFact(TNode atom,
                                bool pol,
                                TNode fact,
                                bool isInternal)
{
  // do nothing for now, but we could be more aggressive
  Trace("arith-eq-solver") << "EqualitySolver::notifyFact: " << fact
                           << std::endl;
  Trace("arith-eq-solver") << "(in state " << d_astate.toString() << ")"
                           << std::endl;
}

bool EqualitySolver::EqualitySolverNotify::eqNotifyTriggerPredicate(
    TNode predicate, bool value)
{
  Trace("arith-eq-solver") << "...propagate (predicate) " << predicate << " -> "
                           << value << std::endl;
  if (value)
  {
    return d_esolver.propagateLit(predicate);
  }
  return d_esolver.propagateLit(predicate.notNode());
}

bool EqualitySolver::EqualitySolverNotify::eqNotifyTriggerTermEquality(
    TheoryId tag, TNode t1, TNode t2, bool value)
{
  Trace("arith-eq-solver") << "...propagate (term eq) " << t1.eqNode(t2)
                           << " -> " << value << std::endl;
  if (value)
  {
    return d_esolver.propagateLit(t1.eqNode(t2));
  }
  return d_esolver.propagateLit(t1.eqNode(t2).notNode());
}

void EqualitySolver::EqualitySolverNotify::eqNotifyConstantTermMerge(TNode t1,
                                                                     TNode t2)
{
  Trace("arith-eq-solver") << "...conflict merge " << t1 << " " << t2
                           << std::endl;
  return d_aim.conflictEqConstantMerge(t1, t2);
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
