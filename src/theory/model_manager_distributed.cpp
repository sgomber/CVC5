/*********************                                                        */
/*! \file ee_manager_distributed.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for equality engines over
 ** all theories.
 **/

#include "theory/model_manager_distributed.h"

#include "options/theory_options.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"

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

  // push/pop to clear the equality engine of the model
  context::Context* meec = d_eem.getModelEqualityEngineContext();
  meec->pop();
  meec->push();

  // Collect model info from the theories
  Trace("model-builder") << "ModelManagerDistributed: Collect model info..."
                         << std::endl;
  if (!collectModelInfo())
  {
    Trace("model-builder") << "ModelManagerDistributed: fail collect model info"
                           << std::endl;
    return false;
  }

  // success is determined by the model builder
  d_modelBuiltSuccess = d_modelBuilder->buildModel(d_model);
  return d_modelBuiltSuccess;
}

}  // namespace theory
}  // namespace CVC4
