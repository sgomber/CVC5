/*********************                                                        */
/*! \file arith_infer_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arithmetic theory state.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__ARITH_INFER_MANAGER_H
#define CVC4__THEORY__ARITH__ARITH_INFER_MANAGER_H

#include "theory/infer_manager.h"
#include "context/cdhashmap.h"

namespace CVC4 {
namespace theory {
namespace arith {

class TheoryArithPrivate;
class EqualitySolver;

/**
 * The arithmetic inference manager.
 */
class ArithInferManager : public InferManager
{
  typedef context::CDHashSet<Node, bool NodeHashFunction> NodeMap;
 public:
  ArithInferManager(Theory& t, TheoryArithPrivate& p, EqualitySolver * es);
  ~ArithInferManager() {}
  /**
   * Return an explanation for the literal represented by parameter n
   * (which was previously propagated by this theory).
   */
  TrustNode explainLit(TNode lit) override;
  /** 
   * Propagate, distinguishes who propagated.
   */
  bool propagateManagedLit(TNode lit, bool fromPrivate=true);
 private:
  /** reference to parent */
  TheoryArithPrivate& d_private;
  /** The (optional) equality solver */
  EqualitySolver * d_esolver;
  /** 
   * Map from literals to whether they were propagated by the private solver.
   * This map is only maintained if we are using an equality solver.
   */
  NodeMap d_propagationMap;
};

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
