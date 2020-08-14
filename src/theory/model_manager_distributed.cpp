/*********************                                                        */
/*! \file model_manager_distributed.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for model generation.
 **/

#include "theory/model_manager_distributed.h"

namespace CVC4 {
namespace theory {

ModelManagerDistributed::ModelManagerDistributed(
    TheoryEngine& te, EqEngineManagerDistributed& eem)
    : ModelManager(te),
      d_eem(eem)
{
}

ModelManagerDistributed::~ModelManagerDistributed() {}

bool ModelManagerDistributed::buildModelInternal()
{
  Trace("model-builder") << "ModelManagerDistributed: reset model..."
                         << std::endl;
  // Reset model
  d_model->reset();

  // push a SAT context

  // Collect model info from the theories
  Trace("model-builder") << "ModelManagerDistributed: Collect model info..."
                         << std::endl;
  bool success = true;
  if (!collectModelInfo())
  {
    Trace("model-builder") << "ModelManagerDistributed: fail collect model info"
                           << std::endl;
    success = false;
  }
  else (!d_modelBuilder->buildModel(d_model))
  {
    success = false;
  }
  
  // pop a SAT context
  
  return success;
}

}  // namespace theory
}  // namespace CVC4
