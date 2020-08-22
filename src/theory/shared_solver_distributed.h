/*********************                                                        */
/*! \file shared_solver_distributed.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Shared solver in distributed architecture.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SHARED_SOLVER_DISTRIBUTED__H
#define CVC4__THEORY__SHARED_SOLVER_DISTRIBUTED__H

#include "expr/node.h"
#include "theory/shared_solver.h"

namespace CVC4 {
namespace theory {

/** 
 * The shared solver in the distributed architecture.
 */
class SharedSolverDistributed : public SharedSolver
{
 public:
  SharedSolverDistributed(TheoryEngine& te);
  virtual ~SharedSolverDistributed() {}
  /**
   * Assert equality to the shared terms database.
   */
  void assertSharedEquality(TNode equality, bool polarity, TNode reason) override;
 protected:
  /** Solver-specific pre-register shared */
  void preRegisterSharedInternal(TNode t) override;
  /** Solver-specific get equality status */
  void getEqualityStatus(TNode t) override;
  /** Solver-specific explain shared */
  void explainSharedInternal(TNode t) override;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SHARED_SOLVER_DISTRIBUTED__H */
