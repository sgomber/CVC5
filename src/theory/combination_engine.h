/*********************                                                        */
/*! \file combination_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Abstract interface for theory combination.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__COMBINATION_ENGINE__H
#define CVC4__THEORY__COMBINATION_ENGINE__H

#include <map>
#include <memory>

#include "theory/ee_manager.h"
#include "theory/model_manager.h"

namespace CVC4 {

class TheoryEngine;
class SharedTermsDatabase;
class SharedTermsVisitor;

namespace theory {

/**
 * Manager for doing theory combination.
 */
class CombinationEngine
{
 public:
  CombinationEngine(TheoryEngine& te, const std::vector<Theory*>& paraTheories);
  virtual ~CombinationEngine();

  /** Finish initialization */
  void finishInit();

  //-------------------------- equality engine
  /** Get the equality engine theory information. */
  const EeTheoryInfo* getEeTheoryInfo(TheoryId tid) const;
  /** get the master equality engine */
  eq::EqualityEngine* getCoreEqualityEngine();
  //-------------------------- end equality engine
  //-------------------------- model
  /** reset model */
  void resetModel();
  /** Build model */
  virtual bool buildModel() = 0;
  /** Post process model */
  void postProcessModel(bool incomplete);
  /** Get model */
  TheoryModel* getModel();
  //-------------------------- end model

  //-------------------------- interface used by theory engine
  /**
   * Combine theories, called after FULL effort passes with no lemmas
   * and before LAST_CALL effort is run. This adds necessary lemmas for
   * theory combination (e.g. splitting lemmas) to the parent TheoryEngine.
   */
  virtual void combineTheories() = 0;
  /**
   * Called when the given term t is pre-registered in TheoryEngine.
   *
   * This adds t as an equality to propagate in the shared terms database
   * if it is an equality, or adds its shared terms if it involves multiple
   * theories.
   *
   * @param t The term to preregister
   * @param multipleTheories Whether multiple theories are present in t.
   */
  virtual void preRegister(TNode t, bool multipleTheories);
  /**
   * Notify assertion fact with the given atom. This is called when any
   * fact is asserted in TheoryEngine, just before it is dispatched to the
   * appropriate theory.
   *
   * This calls Theory::notifySharedTerm for the shared terms of the atom.
   */
  virtual void notifyAssertFact(TNode atom);
  /**
   * Is term a shared term? This is used for debugging.
   */
  virtual bool isShared(TNode term) const;
  /**
   * Get the equality status of a and b, which first asks if the shared
   * terms database as an equality status, and otherwise asks the appropriate
   * Theory.
   *
   * This method is used by ...
   */
  virtual EqualityStatus getEqualityStatus(TNode a, TNode b);
  /**
   * Explain literal, which returns a conjunction of literals that that entail
   * the given one. The shared terms database is used to find this explanation.
   *
   * This method is used by TheoryEngine when it wants an explanation of a
   * propagation that was made by the shared terms database.
   */
  virtual TrustNode explain(TNode literal, TheoryId theory) const;
  /**
   * Assert equality to the shared terms database.
   *
   * This method is called by TheoryEngine when a fact has been marked to
   * send to THEORY_BUILTIN, meaning that shared terms database should
   * maintain this fact. This is the case when ...
   */
  virtual void assertEquality(TNode equality, bool polarity, TNode reason);
  //-------------------------- end interface used by theory engine
 protected:
  /** Send lemma */
  void sendLemma(TNode node, TheoryId atomsTo);
  /** Is theory tid parametric? */
  bool isParametric(TheoryId tid) const;
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** Logic info of theory engine (cached) */
  const LogicInfo& d_logicInfo;
  /** List of parametric theories of theory engine */
  const std::vector<Theory*> d_paraTheories;
  /**
   * The equality engine manager we are using. This class is responsible for
   * configuring equality engines for each theory.
   */
  std::unique_ptr<EqEngineManager> d_eemUse;
  /** The model manager we are using */
  std::unique_ptr<ModelManager> d_mmUse;
  /** The database of shared terms.*/
  std::unique_ptr<SharedTermsDatabase> d_sharedTerms;
  /** Visitor for collecting shared terms */
  std::unique_ptr<SharedTermsVisitor> d_sharedTermsVisitor;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__COMBINATION_DISTRIBUTED__H */
