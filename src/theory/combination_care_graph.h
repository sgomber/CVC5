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
                       const std::vector<Theory*>& paraTheories);
  ~CombinationCareGraph();

  /** Combine theories */
  void combineTheories() override;
  /**
   * Called when the given node is pre-registered in TheoryEngine.
   *
   * This adds node as an equality to propagate in the shared terms database
   * if it is an equality, or adds its shared terms if it involves multiple
   * theories.
   */
  void preRegister(TNode node, bool multipleTheories) override;
  /**
   * Notify assertion fact with the given atom.
   *
   * This calls TheoryEngine::addSharedTermInternal for the shared terms of
   * atom, which in turn calls Theory::addSharedTerm for all relevant theories.
   */
  void notifyAssertFact(TNode atom) override;
  /**
   * Is term a shared term?
   *
   * This is used for debugging.
   */
  bool isShared(TNode term) const override;
  /**
   * Get the equality status of a and b, which first asks if the shared
   * terms database as an equality status, and otherwise asks the appropriate
   * Theory.
   *
   * This method is used by ...
   */
  EqualityStatus getEqualityStatus(TNode a, TNode b) override;
  /**
   * Explain literal, which returns a conjunction of literals that that entail
   * the given one. The shared terms database is used to find this explanation.
   *
   * This method is used by ...
   */
  Node explain(TNode literal) const override;
  /**
   * Assert equality to the shared terms database.
   *
   * This method is called by TheoryEngine when ...
   */
  void assertEquality(TNode equality, bool polarity, TNode reason) override;
  /**
   * The given theory propagated the given literal. Do we need to process it?
   */
  bool needsPropagation(TNode literal, TheoryId theory) override;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__COMBINATION_DISTRIBUTED__H */
