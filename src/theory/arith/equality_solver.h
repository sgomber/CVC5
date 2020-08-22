/*********************                                                        */
/*! \file equality_solver.h
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

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__EQUALITY_SOLVER_H
#define CVC4__THEORY__ARITH__EQUALITY_SOLVER_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "theory/arith/arith_state.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * The arithmetic equality solver.
 */
class EqualitySolver
{
  /** Are we responsible for this propagation? */
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeMap;

 public:
  EqualitySolver(ArithState& astate, InferManager& aim);
  ~EqualitySolver() {}
  //--------------------------------- initialization
  /**
   * Returns true if we need an equality engine, see
   * Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi);
  /**
   * Set equality engine, where ee is a pointer to the official equality engine
   * of theory.
   */
  void setEqualityEngine(eq::EqualityEngine* ee);
  //--------------------------------- end initialization
  /** Pre-notify fact, return true if processed. */
  bool preNotifyFact(TNode atom, bool pol, TNode fact);
  /** Notify fact, return true if processed. */
  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal);
  /**
   * Return an explanation for the literal represented by parameter n
   * (which was previously propagated by this class), or return null trust node
   * if this literal was not propagated by this class.
   */
  TrustNode explainLit(TNode lit);
  /**
   * T-propagate literal lit, encountered by equality engine,
   * returns false if we are in conflict.
   */
  bool propagateLit(TNode lit);
  /**
   * Has propagated (anyone) propagated lit?
   */
  bool hasPropagated(TNode lit) const;
  /**
   * Notify that (another module) propagated lit
   */
  void notifyPropagated(TNode lit);

 private:
  class EqualitySolverNotify : public eq::EqualityEngineNotify
  {
   public:
    EqualitySolverNotify(EqualitySolver& es, InferManager& aim)
        : d_esolver(es), d_aim(aim)
    {
    }

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override;

    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override;

    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override;
    void eqNotifyNewClass(TNode t) override {}
    void eqNotifyMerge(TNode t1, TNode t2) override {}
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override {}

   private:
    /** Reference to the inference manager */
    EqualitySolver& d_esolver;
    /** reference to parent */
    InferManager& d_aim;
  };
  /** reference to the state */
  ArithState& d_astate;
  /** reference to parent */
  InferManager& d_aim;
  /** Equality solver notify */
  EqualitySolverNotify d_notify;
  /** Pointer to the equality engine */
  eq::EqualityEngine* d_ee;
  /** The set of literals we have propagated */
  NodeMap d_propLits;
};

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
