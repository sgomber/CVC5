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
#include "theory/ee_setup_info.h"
#include "theory/uf/equality_engine.h"
#include "theory/trust_node.h"

namespace CVC4 {
namespace theory {
namespace arith {

class ArithInferManager;

/**
 * The arithmetic equality solver.
 */
class EqualitySolver
{
 public:
  EqualitySolver(ArithState& astate, ArithInferManager& aim);
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
   * Return an explanation for the literal lit (which was previously propagated
   * by this solver).
   */
  TrustNode explainLit(TNode lit);

 private:
  class EqualitySolverNotify : public eq::EqualityEngineNotify
  {
   public:
    EqualitySolverNotify(ArithInferManager& aim) : d_aim(aim) {}

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
    /** reference to parent */
    ArithInferManager& d_aim;
  };
  /** reference to the state */
  ArithState& d_astate;
  /** reference to parent */
  ArithInferManager& d_aim;
  /** Equality solver notify */
  EqualitySolverNotify d_notify;
  /** Pointer to the equality engine */
  eq::EqualityEngine* d_ee;
};

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
