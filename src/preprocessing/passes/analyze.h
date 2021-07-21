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

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/arith/bound_inference.h"
#include "util/statistics_stats.h"

#include <iosfwd>

namespace cvc5 {
namespace preprocessing {
namespace passes {


/**
 * Analyze
 */
class Analyze : public PreprocessingPass
{
 public:
  Analyze(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /**
   * Analyze
   */
  void analyze(Node n,
                         std::unordered_set<TNode>& visited);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5

#endif /* CVC5__PREPROCESSING__PASSES__ANALYZE_H */
