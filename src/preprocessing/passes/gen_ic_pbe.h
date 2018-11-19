/*********************                                                        */
/*! \file gen_ic_pbe.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief gen_ic_pbe
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__GEN_IC_PBE_H
#define __CVC4__PREPROCESSING__PASSES__GEN_IC_PBE_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/** GenIcPbe
 * 
 */
class GenIcPbe  : public PreprocessingPass
{
public:
  GenIcPbe(PreprocessingPassContext* preprocContext);
  ~GenIcPbe(){}
protected:
  /**
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__GEN_IC_PBE_H */
