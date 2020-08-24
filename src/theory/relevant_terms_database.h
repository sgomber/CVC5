/*********************                                                        */
/*! \file relevant_terms_database.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Relevant terms database
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__RELEVANT_TERM_DATABASE__H
#define CVC4__THEORY__RELEVANT_TERM_DATABASE__H

#include <set>
#include "expr/node.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * The relevant term database.
 */
class RelevantTermsDatabase
{
 public:
  RelevantTermsDatabase();
  ~RelevantTermsDatabase() {}
  /** reset round, called at the beginning of full effort check */
  void resetRound();
  /** compute */
  void compute();
  /** Is term t a relevant term? */
  bool isRelevant(TNode t) const;
  /** Add relevant term */
  void addRelevantTerm(TNode t);
  /** Get relevant terms */
  const std::set<Node>& getRelevantTerms() const;
  /** clear */
  void clear();
  /**
   * Set irrelevant kind. These kinds do not impact model generation. An
   * example is APPLY_TESTER.
   */
  void setIrrelevantKind(Kind k);
  /**
   * Add all relevant terms in n recursively.
   */
  void addRelevantTermRec(TNode n);
 protected:
  /** The set of relevant terms */
  std::set<Node> d_relevantTerms;
  /** The set of irrelevant kinds */
  std::set<Kind> d_irrKinds;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__TERM_DATABASE__H */
