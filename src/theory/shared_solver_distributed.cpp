/*********************                                                        */
/*! \file ee_manager_distributed.cpp
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

#include "theory/ee_manager_distributed.h"

#include "theory/quantifiers_engine.h"
#include "theory/shared_terms_database.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

SharedSolverDistributed::SharedSolverDistributed(TheoryEngine& te)
    : SharedSolver(te)
{
}

void SharedSolverDistributed::preRegisterSharedInternal(TNode t)
{
  if (t.getKind() == kind::EQUAL)
  {
    // When sharing is enabled, we propagate from the shared terms manager also
    d_sharedTerms->addEqualityToPropagate(t);
  }
}

EqualityStatus SharedSolverDistributed::getEqualityStatus(TNode a, TNode b)
{
  Assert(d_sharedTerms != nullptr);
  // if we're using a shared terms database, ask its status if a and b are
  // shared.
  if (d_sharedTerms->isShared(a) && d_sharedTerms->isShared(b))
  {
    if (d_sharedTerms->areEqual(a, b))
    {
      return EQUALITY_TRUE_AND_PROPAGATED;
    }
    else if (d_sharedTerms->areDisequal(a, b))
    {
      return EQUALITY_FALSE_AND_PROPAGATED;
    }
  }
  return EQUALITY_UNKNOWN;
}

TrustNode SharedSolverDistributed::explainSharedInternal(TNode literal) const
{
  return d_sharedTerms->explain(literal);
}

void SharedSolverDistributed::assertSharedEquality(TNode equality,
                                                      bool polarity,
                                                      TNode reason)
{
  d_sharedTerms->assertEquality(equality, polarity, reason);
}

}  // namespace theory
}  // namespace CVC4
