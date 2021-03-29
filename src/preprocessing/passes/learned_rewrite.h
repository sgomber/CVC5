/*********************                                                        */
/*! \file delay_expand_def.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriting based on learned literals
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__LEARNED_REWRITE_H
#define CVC4__PREPROCESSING__PASSES__LEARNED_REWRITE_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/arith/bound_inference.h"
#include "theory/trust_node.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/**
 * Applies "delayed expand definitions", which eliminates purification UF
 * for kinds.
 */
class LearnedRewrite : public PreprocessingPass
{
 public:
  LearnedRewrite(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /**
   * Apply rewrite with learned literals.
   */
  Node rewriteLearnedRec(Node n, theory::arith::BoundInference& binfer);
  /**
   * Learned rewrite
   */
  Node rewriteLearned(Node n, theory::arith::BoundInference& binfer);
  /** Return learned rewrite */
  Node returnRewriteLearned(Node n, Node nr, const char* c);
  /** static upper/lower bounds */
  std::map<Node, std::pair<Node, Node> > d_bounds;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__LEARNED_REWRITE_H */
