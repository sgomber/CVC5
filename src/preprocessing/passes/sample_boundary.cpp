/*********************                                                        */
/*! \file sample_boundary.cpp
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

#include "preprocessing/passes/sample_boundary.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

SampleBoundary::SampleBoundary(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "sample-boundary"){};

PreprocessingPassResult SampleBoundary::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{


  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
