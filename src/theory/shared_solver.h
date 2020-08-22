/*********************                                                        */
/*! \file shared_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for shared solver
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SHARED_SOLVER__H
#define CVC4__THEORY__SHARED_SOLVER__H

#include "expr/node.h"
#include "theory/shared_terms_database.h"
#include "theory/term_registration_visitor.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Virtual base class for shared solver. This is the component of theory
 * engine that behaves like a theory solver whose purpose is to ensure the
 * main theory combination method can be performed (in CombinationEngine).
 * Its role is to as necessary:
 * (1) Notify the individual theories of shared terms via addSharedTerms,
 * (2) Be the official standard for equality statuses,
 * (3) Propagate equalities when necessary and explain them.
 */
class SharedSolver
{
 public:
  SharedSolver(TheoryEngine& te);
  virtual ~SharedSolver() {}
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
  void preRegisterShared(TNode t, bool multipleTheories);
  /**
   * Pre-notify assertion fact with the given atom. This is called when any
   * fact is asserted in TheoryEngine, just before it is dispatched to the
   * appropriate theory.
   *
   * This calls Theory::notifySharedTerm for the shared terms of the atom.
   */
  void preNotifySharedFact(TNode atom);
  /**
   * Get the equality status of a and b, which first asks if the shared
   * terms database as an equality status, and otherwise asks the appropriate
   * Theory.
   *
   * This method is used by theories via Valuation mostly for determining their
   * care graph.
   */
  EqualityStatus getEqualityStatus(TNode a, TNode b);
  /**
   * Explain literal, which returns a conjunction of literals that that entail
   * the given one. The shared terms database is used to find this explanation.
   *
   * This method is used by TheoryEngine when it wants an explanation of a
   * propagation that was made by the shared terms database.
   */
  TrustNode explainShared(TNode literal, TheoryId theory) const;
  /**
   * Assert equality to the shared terms database.
   *
   * This method is called by TheoryEngine when a fact has been marked to
   * send to THEORY_BUILTIN, meaning that shared terms database should
   * maintain this fact. This is the case when ...
   */
  virtual void assertSharedEquality(TNode equality,
                                    bool polarity,
                                    TNode reason);

 protected:
  /** Solver-specific pre-register shared */
  virtual void preRegisterShared(TNode t) = 0;
  /** Solver-specific get equality status */
  virtual void getEqualityStatusInternal(TNode t) = 0;
  /** Solver-specific explain shared */
  virtual void explainSharedInternal(TNode t) = 0;
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** Logic info of theory engine (cached) */
  const LogicInfo& d_logicInfo;
  /** The database of shared terms.*/
  SharedTermsDatabase d_sharedTerms;
  /** Visitor for collecting shared terms */
  SharedTermsVisitor d_sharedTermsVisitor;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__EE_MANAGER__H */
