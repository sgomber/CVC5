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
 ** \brief Arithmetic inference manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__ARITH_INFER_MANAGER_H
#define CVC4__THEORY__ARITH__ARITH_INFER_MANAGER_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "theory/inference_manager.h"

namespace CVC4 {
namespace theory {
namespace arith {

class TheoryArithPrivate;
class EqualitySolver;

/**
 * The arithmetic inference manager.
 */
class ArithInferManager : public TheoryInferenceManager
{
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeMap;

 public:
  ArithInferManager(Theory& t,
                    TheoryState& state,
                    TheoryArithPrivate& p,
                    ProofNodeManager* pnm);
  ~ArithInferManager() {}
  /** Set equality solver */
  void setEqualitySolver(EqualitySolver* es);
  /**
   * Return an explanation for the literal represented by parameter n
   * (which was previously propagated by this theory).
   */
  TrustNode explainLit(TNode lit) override;
  /**
   * Propagate, which tracks who propagated if there are multiple possible
   * sources.
   */
  bool propagateManagedLit(TNode lit, bool fromPrivate = true);

 private:
  /** reference to parent */
  TheoryArithPrivate& d_private;
  /** The (optional) equality solver */
  EqualitySolver* d_esolver;
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
