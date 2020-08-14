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

#include "theory/ee_manager_distributed.h"
#include "theory/model_manager_distributed.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Manager for doing theory combination.
 */
class CombinationEngine
{
 public:
  CombinationEngine(TheoryEngine& te,
                       const std::vector<Theory*>& paraTheories,
                       context::Context* c);
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
  bool buildModel();
  /** Post process model */
  void postProcessModel(bool incomplete);
  /** Get model */
  TheoryModel* getModel();
  //-------------------------- end model

  //-------------------------- interface used by theory engine
  /** Combine theories */
  virtual void combineTheories();
  virtual void preRegister(TNode preprocessed);
  virtual void notifyAssertFact(TNode atom);
  virtual bool isShared(TNode term) const;
  virtual EqualityStatus getEqualityStatus(TNode a, TNode b);
  virtual Node explain(TNode literal) const;
  virtual void assertEquality(TNode equality, bool polarity, TNode reason);
  /**
   * The given theory propagated the given literal. Do we need to process it?
   */
  virtual bool needsPropagation(TNode literal, TheoryId theory);
  //-------------------------- end interface used by theory engine
 protected:
  /** 
   * Initialize internal, which is responsible for constructing the equality
   * engine and model managers (d_eemUse and d_mmUse) based on the options.
   */
  virtual void initializeInternal();
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
  EqEngineManager* d_eemUse;
  /** The model manager we are using */
  ModelManager* d_mmUse;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__COMBINATION_DISTRIBUTED__H */
