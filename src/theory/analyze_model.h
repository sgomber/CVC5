/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Analyze model utility
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ANALYZE_MODEL__H
#define CVC5__THEORY__ANALYZE_MODEL__H

#include <unordered_map>
#include <unordered_set>

#include "expr/node.h"
#include "theory/valuation.h"

namespace cvc5 {
namespace theory {

class TheoryModel;
class RelevanceManager;

/**
 */
class AnalyzeModel
{
 public:
  AnalyzeModel(Valuation val, RelevanceManager * rm, TheoryModel * tm);
  /** Debug model failure */
  void analyzeModelFailure();
 private:
   /** Get or assign id for literal */
   size_t getOrAssignIdFor(Node lit);
  /** The valuation object, used to query current value of theory literals */
  Valuation d_val;
  /** The relevance manager */
  RelevanceManager * d_rm;
  /** The theory model */
  TheoryModel * d_model;
  /** Assigning literals to identifiers */
  std::map< Node, size_t > d_litId;
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ANALYZE_MODEL__H */
