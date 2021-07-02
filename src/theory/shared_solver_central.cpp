/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Shared solver for central equality engine architecture
 */

#include "theory/shared_solver_central.h"

#include "theory/theory_engine.h"

namespace cvc5 {
namespace theory {

SharedSolverCentral::SharedSolverCentral(TheoryEngine& te,
                                         ProofNodeManager* pnm)
    : SharedSolver(te, pnm), d_centralEe(nullptr)
{
}

bool SharedSolverCentral::needsEqualityEngine(theory::EeSetupInfo& esi)
{
  return d_sharedTerms.needsEqualityEngine(esi);
}

void SharedSolverCentral::setEqualityEngine(eq::EqualityEngine* ee)
{
  d_sharedTerms.setEqualityEngine(ee);
  d_centralEe = ee;
}

void SharedSolverCentral::preRegisterSharedInternal(TNode t)
{
  if (t.getKind() == kind::EQUAL)
  {
    // When sharing is enabled, we propagate from the shared terms manager also
    d_sharedTerms.addEqualityToPropagate(t);
  }
}

EqualityStatus SharedSolverCentral::getEqualityStatus(TNode a, TNode b)
{
  // if we're using a shared terms database, ask its status if a and b are
  // shared.
  if (d_sharedTerms.isShared(a) && d_sharedTerms.isShared(b))
  {
    if (d_sharedTerms.areEqual(a, b))
    {
      return EQUALITY_TRUE_AND_PROPAGATED;
    }
    else if (d_sharedTerms.areDisequal(a, b))
    {
      return EQUALITY_FALSE_AND_PROPAGATED;
    }
  }
  // otherwise, ask the theory
  return d_te.theoryOf(Theory::theoryOf(a.getType()))->getEqualityStatus(a, b);
}

TrustNode SharedSolverCentral::explain(TNode literal, TheoryId id)
{
  TrustNode texp;
  Trace("shared-solver") << "SharedSolverCentral::explain: " << literal << " "
                         << id << std::endl;
  if (id == THEORY_BUILTIN)
  {
    Node exp = d_centralEe->mkExplainLit(literal);
    texp = TrustNode::mkTrustPropExp(literal, exp, nullptr);
    Trace("shared-solver")
        << "\tTerm was propagated by THEORY_BUILTIN. Explanation: " << exp
        << std::endl;
  }
  else
  {
    // By default, we ask the individual theory for the explanation.
    // It is possible that a centralized approach could preempt this.
    texp = d_te.theoryOf(id)->explain(literal);
    Trace("shared-solver") << "\tTerm was propagated by owner theory: " << id
                           << ". Explanation: " << texp.getNode() << std::endl;
  }
  return texp;
}

void SharedSolverCentral::assertSharedEquality(TNode equality,
                                               bool polarity,
                                               TNode reason)
{
  d_sharedTerms.assertEquality(equality, polarity, reason);
}

}  // namespace theory
}  // namespace cvc5
