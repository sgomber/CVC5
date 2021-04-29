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
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__ELIM_TYPES_H
#define CVC5__PREPROCESSING__PASSES__ELIM_TYPES_H

#include <unordered_set>
#include <map>

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

class ElimTypes : public PreprocessingPass
{
 public:
  ElimTypes(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /** Collect types in node n */
  void collectTypes(const Node& n,
                    std::unordered_set<TNode, TNodeHashFunction>& visited,
                    std::unordered_set<TypeNode, TypeNodeHashFunction>& types,
                    std::map<TypeNode, std::vector<Node>>& sym);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5

#endif /* CVC5__PREPROCESSING__PASSES__ELIM_TYPES_H */
