/*********************                                                        */
/*! \file sample_boundary.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sample boundary
 **/

#ifndef __CVC4__PREPROCESSING__PASSES__SAMPLE_BOUNDARY_H_
#define __CVC4__PREPROCESSING__PASSES__SAMPLE_BOUNDARY_H_

#include <map>
#include <string>
#include <vector>
#include "expr/node.h"

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/**
 * This class 
 */
class SampleBoundary : public PreprocessingPass
{
 public:
  SampleBoundary(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /** process internal */
  Node convert(TNode n, std::unordered_map<Node, Node, NodeHashFunction>& cache, std::unordered_map<Node, bool, NodeHashFunction>& hasSampling);
  /** is k a bool connective? */
  static bool isBoolConnective( Kind k );
  /** is n a bool connective term? */
  static bool isBoolConnectiveTerm( TNode n );
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__SYMMETRY_BREAKER_H_ */
