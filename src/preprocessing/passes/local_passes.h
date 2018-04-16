/*********************                                                        */
/*! \file local_passes.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The set of local preprocessing passes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__LOCAL_PASSES_H
#define __CVC4__PREPROCESSING__PASSES__LOCAL_PASSES_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/*
class LocalPassState
{
public:
  
};
*/
  
/** Local pass
 * 
 * TODO
 */
class LocalPass
{
public:
  virtual Node preprocess( Node n, bool has_pol, bool has_epol, bool pol ) = 0;
  virtual Node postprocess( Node n, bool has_pol, bool has_epol, bool pol ) = 0;
};
  
class LocalPasses : public PreprocessingPass
{
  /** return the (integer) cache value for the polarity information */
  static inline int polToCVal( bool has_pol, bool has_epol, bool pol );
  /** get the polarity information for the cache value */
  static inline void cValToPol( int cvalue, bool& has_pol, bool& has_epol, bool& pol );
  /** get new polarity information for the i^th child of a node of Kind k
   * 
   * We assume that the current context has polarity.
   * This updates the values of new_has_pol, new_has_epol, new_pol 
   */
  static inline void getPol(Kind k, unsigned i, bool has_epol, bool pol, bool& new_has_pol, bool& new_has_epol, bool& new_pol);
 public:
  LocalPasses(PreprocessingPassContext* preprocContext);

  /** register a local pass */
  void registerLocalPass( LocalPass * lp );
 protected:
  /** the state */
  //LocalPassState d_state;
  /** list of local passes */
  std::vector< LocalPass * > d_lps;
  /** apply internal */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /** simplify assertion */
  Node simplifyAssertion( Node n );
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__LOCAL_PASSES_H */
