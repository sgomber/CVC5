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
#include "util/rational.h"
#include "smt/preprocess_proof_generator.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

AndElim::AndElim(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "and-elim"), 
      d_lcp(d_env.getProofNodeManager() ? new LazyCDProof(
                 d_env.getProofNodeManager(), nullptr, userContext(), "AndElim::lcp")
                   : nullptr)
{
}

PreprocessingPassResult AndElim::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager * nm = NodeManager::currentNM();
  size_t size = assertionsToPreprocess->size();
  size_t i = 0;
  while (i < size)
  {
    Node a = (*assertionsToPreprocess)[i];
    if (a.getKind()==kind::AND)
    {
      if (isProofEnabled())
      {
        smt::PreprocessProofGenerator * pppg = assertionsToPreprocess->getPreprocessProofGenerator();
        d_lcp->addProof(pppg->getProofFor(a));
        for (size_t j=0, achild = a.getNumChildren(); j<achild; j++)
        {
          Node nj = nm->mkConstInt(Rational(j));
          d_lcp->addStep(a[j], PfRule::AND_ELIM, {a}, {nj});
        }
      }
      assertionsToPreprocess->replace(i, a[0], d_lcp.get());
      for (size_t j=1, achild = a.getNumChildren(); j<achild; j++)
      {
        assertionsToPreprocess->push_back(a[j], d_lcp.get());
      }
    }
    else
    {
      i = i+1;
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

bool AndElim::isProofEnabled() const
{
  return d_lcp!=nullptr;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
