/*********************                                                        */
/*! \file ee_manager_central.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for equality sharing.
 **/

#include "theory/ee_manager_central.h"

#include "theory/quantifiers_engine.h"
#include "theory/shared_terms_database.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

SharedSolverCentral::SharedSolverCentral(TheoryEngine& te)
    : SharedSolver(te), d_centralEe(nullptr)
{
}

SharedSolverCentral::~SharedSolverCentral() {}

bool SharedSolverDistributed:: needsEqualityEngine(theory::EeSetupInfo& esi)
{
  return true;
}

void SharedSolverDistributed::setEqualityEngine(eq::EqualityEngine* ee)
{
  d_centralEe = ee;
}

EqualityStatus SharedSolverCentral::getEqualityStatus(TNode a, TNode b)
{
  if (d_centralEe->hasTerm(a) && d_centralEe->hasTerm(b))
  {
    // Check for equality (simplest)
    if (d_centralEe->areEqual(a, b))
    {
      // The terms are implied to be equal
      return EQUALITY_TRUE;
    }
    // Check for disequality
    if (d_centralEe->areDisequal(a, b, false))
    {
      // The terms are implied to be dis-equal
      return EQUALITY_FALSE;
    }
  }
  return EQUALITY_UNKNOWN;
}

TrustNode SharedSolverCentral::explainShared(TNode literal) const
{
  Node exp = d_centralEe->mkExplainLit(literal);
  return TrustNode::mkTrustPropExp(literal, exp, nullptr);
}

void SharedSolverCentral::assertSharedEquality(TNode equality,
                                                  bool polarity,
                                                  TNode reason)
{
  d_centralEe->assertEquality(equality, polarity, reason);
}

}  // namespace theory
}  // namespace CVC4
