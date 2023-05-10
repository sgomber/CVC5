/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Apply substitutions preprocessing pass.
 *
 * Apply top level substitutions to assertions, rewrite, and store back into
 * assertions.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__ASSIGNER_INFER_H
#define CVC5__PREPROCESSING__PASSES__ASSIGNER_INFER_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {

class PreprocessingPassContext;

namespace passes {

class AssignerInfer : public PreprocessingPass
{
 public:
  AssignerInfer(PreprocessingPassContext* preprocContext);

 protected:
  /**
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /** convert to assigner */
  Node convertToAssigner(std::unordered_map<TNode, Node> visited,
                         const Node& n,
                         std::vector<Node>& lemmas);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
