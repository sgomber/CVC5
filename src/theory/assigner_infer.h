/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Relevance manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ASSIGNER_INFER__H
#define CVC5__THEORY__ASSIGNER_INFER__H

#include <unordered_set>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {

/**
 */
class AssignerInference : protected EnvObj
{
 public:
  /**
   * @param env The environment
   * @param engine The parent theory engine
   */
  AssignerInference(Env& env);
  /**
   * Notify (preprocessed) assertions. This is called for input formulas or
   * lemmas that need justification that have been fully processed, just before
   * adding them to the PropEngine.
   *
   * @param assertions The assertions
   */
  void notifyPreprocessedAssertions(const std::vector<Node>& assertions);
 private:
  /** convert to assigner */
  void registerAssigners(std::unordered_set<Node>& visited,
                         const Node& n);
  static Node getSymbolsHash(const Node& n);
  bool registerAssigner(const Node& n);
  /** Total number of assigners found */
  IntStat d_numAssigners;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ASSIGNER_INFER__H */
