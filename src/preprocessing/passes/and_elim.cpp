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

#include "preprocessing/passes/and_elim.h"

#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/env.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

AndElim::AndElim(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "and-elim")
{
}

PreprocessingPassResult AndElim::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  theory::TrustSubstitutionMap& tlsm =
      d_preprocContext->getTopLevelSubstitutions();
  size_t size = assertionsToPreprocess->size();
  while (i < size)
  {
    Node a = (*assertionsToPreprocess)[i];
    if (a.getKind()==kind::AND)
    {
      assertionsToPreprocess->replace(i, a[0]);
      for (size_t j=1, achild = a.getNumChildren(); j<achild; j++)
      {
        assertionsToPreprocess->push_back(a[j]);
      }
    }
    else
    {
      i = i+1;
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
