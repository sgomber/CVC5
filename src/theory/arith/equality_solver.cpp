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

#include "theory/arith/arith_infer_manager.h"
#include "theory/arith/theory_arith.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

EqualitySolver::EqualitySolver(ArithState& astate, ArithInferManager& aim)
    : d_astate(astate), d_aim(aim), d_notify(aim), d_ee(nullptr)
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

TrustNode EqualitySolver::explainLit(TNode lit)
{
  // just explain with equality engine for now
  Node exp = d_ee->mkExplainLit(lit);
  return TrustNode::mkTrustPropExp(lit, exp, nullptr);
}

bool EqualitySolver::EqualitySolverNotify::eqNotifyTriggerPredicate(
    TNode predicate, bool value)
{
  Trace("arith-eq-solver") << "...propagate (predicate) " << predicate << " -> "
                           << value << std::endl;
  if (value)
  {
    return d_aim.propagateManagedLit(predicate, false);
  }
  return d_aim.propagateManagedLit(predicate.notNode(), false);
}

bool EqualitySolver::EqualitySolverNotify::eqNotifyTriggerTermEquality(
    TheoryId tag, TNode t1, TNode t2, bool value)
{
  Trace("arith-eq-solver") << "...propagate (term eq) " << t1.eqNode(t2)
                           << " -> " << value << std::endl;
  if (value)
  {
    return d_aim.propagateManagedLit(t1.eqNode(t2), false);
  }
  return d_aim.propagateManagedLit(t1.eqNode(t2).notNode(), false);
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
