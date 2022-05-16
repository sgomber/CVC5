/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * And elimination
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__AND_ELIM_H
#define CVC5__PREPROCESSING__PASSES__AND_ELIM_H

#include "preprocessing/preprocessing_pass.h"
#include "proof/lazy_proof.h"

namespace cvc5::internal {
namespace preprocessing {

class PreprocessingPassContext;

namespace passes {

class AndElim : public PreprocessingPass
{
 public:
  AndElim(PreprocessingPassContext* preprocContext);

 protected:
  /**
   * Ensure that no top-level assertions are AND.
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /**
   */
  std::unique_ptr<LazyCDProof> d_lazy;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
