/*********************                                                        */
/*! \file model_manager_central.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a central approach for model generation.
 **/

#include "theory/model_manager_central.h"

#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

ModelManagerCentral::ModelManagerCentral(TheoryEngine& te) : ModelManager(te) {}

ModelManagerCentral::~ModelManagerCentral() {}

bool ModelManagerCentral::buildModelInternal()
{
  Trace("model-builder") << "ModelManagerCentral: reset model..." << std::endl;
  // Reset model
  d_model->reset();

  // must compute relevant terms
  std::set<Node> relevantTerms;
  for (TheoryId theoryId = theory::THEORY_FIRST;
       theoryId != theory::THEORY_LAST;
       ++theoryId)
  {
    Theory* t = d_te.theoryOf(theoryId);
    if (t == nullptr)
    {
      // theory not active, skip
      continue;
    }
    // compute relevant terms
    t->computeRelevantTerms(relevantTerms);
  }
  // we use relevant terms based on the above set
  d_model->setUsingRelevantTerms();
  for (const Node& t : relevantTerms)
  {
    d_model->addRelevantTerm(t);
  }
  
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
  else if (!d_modelBuilder->buildModel(d_model))
  {
    Trace("model-builder") << "ModelManagerCentral: fail build model"
                           << std::endl;
    success = false;
  }

  // pop a SAT context
  c->pop();

  return success;
}

}  // namespace theory
}  // namespace CVC4
