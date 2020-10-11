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
 ** \brief Delayed expand definitions
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__DELAY_EXPAND_DEF_H
#define CVC4__PREPROCESSING__PASSES__DELAY_EXPAND_DEF_H

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
class DelayExpandDefs : public PreprocessingPass
{
 public:
  DelayExpandDefs(PreprocessingPassContext* preprocContext);

 protected:
  typedef std::unordered_set<
      std::pair<Node, uint32_t>,
      PairHashFunction<Node, uint32_t, NodeHashFunction> >
      ExtPolNodeCache;
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /**
   * Apply expand delayed definitions, which replaces APPLY_UF that purify
   * builtin kinds with their original operators.
   */
  Node expandDelayedDefinitions(Node n, theory::arith::BoundInference& binfer);
  /**
   * Delayed rewrite
   */
  Node rewriteDelayed(Node n, theory::arith::BoundInference& binfer);
  /** static upper/lower bounds */
  std::map<Node, std::pair<Node, Node> > d_bounds;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__DELAY_EXPAND_DEF_H */
