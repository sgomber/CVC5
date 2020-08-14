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

#include "theory/combination_engine.h"
#include "theory/shared_terms_database.h"
#include "theory/term_registration_visitor.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Manager for doing theory combination using care graphs. This is typically
 * done via a distributed equalty engine architecture.
 */
class CombinationCareGraph : public CombinationEngine
{
 public:
  CombinationCareGraph(TheoryEngine& te,
                       const std::vector<Theory*>& paraTheories,
                       context::Context* c);
  ~CombinationCareGraph();

  /** Combine theories */
  void combineTheories() override;
  void preRegister(TNode preprocessed) override;
  void notifyAssertFact(TNode atom) override;
  bool isShared(TNode term) const override;
  EqualityStatus getEqualityStatus(TNode a, TNode b) override;
  Node explain(TNode literal) const override;
  void assertEquality(TNode equality, bool polarity, TNode reason) override;
  /**
   * The given theory propagated the given literal. Do we need to process it?
   */
  bool needsPropagation(TNode literal, TheoryId theory) override;

 private:
  /**
   * Initialize internal, which is responsible for constructing the equality
   * engine and model managers (d_eemUse and d_mmUse) based on the options.
   */
  void initializeInternal() override;
  /**
   * The database of shared terms.
   */
  SharedTermsDatabase d_sharedTerms;

  /** Default visitor for pre-registration */
  PreRegisterVisitor d_preRegistrationVisitor;

  /** Visitor for collecting shared terms */
  SharedTermsVisitor d_sharedTermsVisitor;
  /**
   * Equality engine manager for handling equalties in a "distributed" fashion,
   * i.e. each theory maintains a unique instance of an equality engine.
   */
  std::unique_ptr<EqEngineManagerDistributed> d_eeDistributed;
  /**
   * The distributed model manager, which maintains its own equality engine
   * which other theories dump to after a FULL effort check.
   */
  std::unique_ptr<ModelManagerDistributed> d_mDistributed;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__COMBINATION_DISTRIBUTED__H */
