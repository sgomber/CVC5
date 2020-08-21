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

namespace CVC4 {
namespace theory {
namespace arith {

EqualitySolver::EqualitySolver(InferManager& aim, ArithState& astate) : d_aim(aim), d_astate(astate), d_notify(aim), d_ee(nullptr){
  
}

bool EqualitySolver::needsEqualityEngine(EeSetupInfo& esi)
{
  
}
void EqualitySolver::setEqualityEngine(eq::EqualityEngine* ee)
{
  
}
bool EqualitySolver::preNotifyFact(TNode atom, bool pol, TNode fact)
{
  
}
void EqualitySolver::notifyFact(TNode atom, bool pol, TNode fact, bool isInternal)
{
  
}

bool EqualitySolver::EqualitySolverNotify::eqNotifyTriggerPredicate(TNode predicate, bool value)
{
  
}

bool EqualitySolver::EqualitySolverNotify::eqNotifyTriggerTermEquality(TheoryId tag,
                                  TNode t1,
                                  TNode t2,
                                  bool value)
{
  
}

void EqualitySolver::EqualitySolverNotify::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
