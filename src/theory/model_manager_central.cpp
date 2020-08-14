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

#include "theory/model_manager_central.h"

#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

ModelManagerCentral::ModelManagerCentral(
    TheoryEngine& te, EqEngineManagerDistributed& eem)
    : ModelManager(te),
      d_eem(eem)
{
}

ModelManagerCentral::~ModelManagerCentral() {}

bool ModelManagerCentral::buildModelInternal()
{
  Trace("model-builder") << "ModelManagerCentral: reset model..."
                         << std::endl;
  // Reset model
  d_model->reset();

  // push a SAT context
  context::Context* c = d_te.getSatContext();
  c->push();

  // Collect model info from the theories
  Trace("model-builder") << "ModelManagerCentral: Collect model info..."
                         << std::endl;
  bool success = true;
  if (!collectModelInfo())
  {
    Trace("model-builder") << "ModelManagerCentral: fail collect model info"
                           << std::endl;
    success = false;
  }
  else (!d_modelBuilder->buildModel(d_model))
  {
    success = false;
  }
  
  // pop a SAT context
  c->pop();
  
  return success;
}

}  // namespace theory
}  // namespace CVC4
