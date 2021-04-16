/*********************                                                        */
/*! \file shared_solver_test.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC5 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Shared solver in the test architecture.
 **/

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SHARED_SOLVER_TEST__H
#define CVC5__THEORY__SHARED_SOLVER_TEST__H

#include "expr/node.h"
#include "theory/shared_solver.h"

namespace cvc5 {
namespace theory {

/**
 * The shared solver in the test architecture.
 */
class SharedSolverTest : public SharedSolver
{
 public:
  SharedSolverTest(TheoryEngine& te, ProofNodeManager* pnm);
  virtual ~SharedSolverTest() {}
  //------------------------------------- initialization
  /**
   * Returns true if we need an equality engine, this has the same contract
   * as Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(theory::EeSetupInfo& esi) override;
  /** Set equality engine in the shared terms database */
  void setEqualityEngine(eq::EqualityEngine* ee) override;
  //------------------------------------- end initialization
  /** Assert equality to the shared terms database. */
  void assertSharedEquality(TNode equality,
                            bool polarity,
                            TNode reason) override;
  /**
   * Get equality status based on the equality engine of shared terms database
   */
  EqualityStatus getEqualityStatus(TNode a, TNode b) override;
  /** Explain literal that was propagated by a theory or using shared terms
   * database */
  TrustNode explain(TNode literal, TheoryId id) override;

 protected:
  /** If t is an equality, add it as one that may be propagated */
  void preRegisterSharedInternal(TNode t) override;
  /** Pointer to the central equality engine */
  eq::EqualityEngine* d_centralEe;
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__SHARED_SOLVER_TEST__H */
