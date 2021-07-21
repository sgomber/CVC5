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
 * Rewriting based on learned literals
 */
#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__ANALYZE_H
#define CVC5__PREPROCESSING__PASSES__ANALYZE_H

#include "expr/node.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

/**
 * Analyze
 */
class AnalyzeConstants
{
 public:
  AnalyzeConstants();

  /** Analyze constants */
  void analyzeConstants(TypeNode tn, const std::vector<Node>& cs);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5

#endif /* CVC5__PREPROCESSING__PASSES__ANALYZE_H */
