/*********************                                                        */
/*! \file ee_manager_distributed.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for equality engines over
 ** all theories.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__EE_MANAGER_CENTRAL__H
#define CVC4__THEORY__EE_MANAGER_CENTRAL__H

#include "theory/ee_manager.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {

class TheoryEngine;
class SharedTermsDatabase;

namespace theory {

/**
 * The (central) equality engine manager. This encapsulates an architecture
 * in which all theories use a common central equality engine.
 */
class EqEngineManagerCentral : public EqEngineManager
{
 public:
  EqEngineManagerCentral(TheoryEngine& te);
  ~EqEngineManagerCentral();
  /**
   * Initialize theories
   */
  void initializeTheories(SharedSolver* sharedSolver) override;
  /**
   * Initialize model.
   */
  void initializeModel(TheoryModel* m,
                       eq::EqualityEngineNotify* notify) override;
  /** get the core equality engine */
  eq::EqualityEngine* getCoreEqualityEngine() override;
  /** get the model equality engine */
  eq::EqualityEngine* getModelEqualityEngine() override;

 private:
  /**
   * Notify class for central equality engine. This class dispatches
   * notifications from the central equality engine to the appropriate
   * theory(s).
   */
  class CentralNotifyClass : public theory::eq::EqualityEngineNotify
  {
   public:
    CentralNotifyClass(EqEngineManagerCentral& eemc);
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override;
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override;
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override;
    void eqNotifyNewClass(TNode t) override;
    void eqNotifyMerge(TNode t1, TNode t2) override;
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override;
    /** Parent */
    EqEngineManagerCentral& d_eemc;
    /** List of notify classes that need new class notification */
    std::vector<eq::EqualityEngineNotify*> d_newClassNotify;
    /** List of notify classes that need merge notification */
    std::vector<eq::EqualityEngineNotify*> d_mergeNotify;
    /** List of notify classes that need disequality notification */
    std::vector<eq::EqualityEngineNotify*> d_disequalNotify;
    /** The model notify class */
    eq::EqualityEngineNotify* d_mNotify;
    /** The quantifiers engine */
    QuantifiersEngine* d_quantEngine;
  };
  /** Notification when predicate gets value in central equality engine */
  bool eqNotifyTriggerPredicate(TNode predicate, bool value);
  /** Notification when constants are merged in central equality engine */
  void eqNotifyConstantTermMerge(TNode t1, TNode t2);
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** The central equality engine notify class */
  CentralNotifyClass d_centralEENotify;
  /** The central equality engine. */
  eq::EqualityEngine d_centralEqualityEngine;
  /**
   * A table of from theory IDs to notify classes.
   */
  eq::EqualityEngineNotify* d_theoryNotify[theory::THEORY_LAST];
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__EE_MANAGER_CENTRAL__H */
