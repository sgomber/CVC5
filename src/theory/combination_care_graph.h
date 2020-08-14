/*********************                                                        */
/*! \file combination_care_graph.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a care graph based approach for theory combination.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__COMBINATION_CARE_GRAPH__H
#define CVC4__THEORY__COMBINATION_CARE_GRAPH__H

#include <map>
#include <memory>

#include "theory/ee_manager_distributed.h"
#include "theory/model_manager_distributed.h"
#include "theory/shared_terms_database.h"
#include "theory/term_registration_visitor.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Manager for doing theory combination in a distributed architecture.
 */
class CombinationCareGraph
{
 public:
  CombinationCareGraph(TheoryEngine& te,
                       const std::vector<Theory*>& paraTheories,
                       context::Context* c);
  ~CombinationCareGraph();
  /** Finish initialization */
  void finishInit();
  //-------------------------- equality engine
  /** Get the equality engine theory information. */
  const EeTheoryInfo* getEeTheoryInfo(TheoryId tid) const;
  /** get the master equality engine */
  eq::EqualityEngine* getMasterEqualityEngine();
  //-------------------------- end equality engine
  //-------------------------- model
  /** reset model */
  void resetModel();
  /** Build model */
  bool buildModel();
  /** Post process model */
  void postProcessModel(bool incomplete);
  /** Get model */
  theory::TheoryModel* getModel();
  //-------------------------- end model

  //-------------------------- interface used by theory engine
  /** Combine theories */
  void combineTheories();
  void preRegister(TNode preprocessed);
  void notifyAssertFact(TNode atom);
  bool isShared(TNode term) const;
  theory::EqualityStatus getEqualityStatus(TNode a, TNode b);

  Node explain(TNode literal) const;
  void assertEquality(TNode equality, bool polarity, TNode reason);
  //-------------------------- end interface used by theory engine
 private:
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** Logic info of theory engine (cached) */
  const LogicInfo& d_logicInfo;
  /** List of parametric theories of theory engine */
  const std::vector<Theory*> d_paraTheories;
  /**
   * The database of shared terms.
   */
  SharedTermsDatabase d_sharedTerms;

  /** Default visitor for pre-registration */
  PreRegisterVisitor d_preRegistrationVisitor;

  /** Visitor for collecting shared terms */
  SharedTermsVisitor d_sharedTermsVisitor;

  /**
   * The distributed equality manager. This class is responsible for
   * configuring the theories of this class for handling equalties
   * in a "distributed" fashion, i.e. each theory maintains a unique
   * instance of an equality engine. These equality engines are memory
   * managed by this class.
   */
  std::unique_ptr<theory::EqEngineManagerDistributed> d_eeDistributed;

  /** The model manager */
  std::unique_ptr<theory::ModelManagerDistributed> d_mDistributed;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__COMBINATION_DISTRIBUTED__H */
