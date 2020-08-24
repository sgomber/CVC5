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

bool ModelManagerCentral::prepareModel()
{
  Trace("model-builder") << "ModelManagerCentral: reset model..." << std::endl;

  // push a SAT context
  context::Context* c = d_te.getSatContext();
  c->push();

  // Collect model info from the theories
  Trace("model-builder") << "ModelManagerCentral: Collect model values..."
                         << std::endl;
  // Consult each active theory to get all relevant information concerning the
  // model, which includes both dump their equality information and assigning
  // values.
  for (TheoryId theoryId = theory::THEORY_FIRST; theoryId < theory::THEORY_LAST;
       ++theoryId)
  {
    if (!d_logicInfo.isTheoryEnabled(theoryId))
    {
      // theory not active, skip
      continue;
    }
    Theory* t = d_te.theoryOf(theoryId);
    // collect the asserted terms
    std::set<Node> termSet;
    collectAssertedTerms(theoryId, termSet);
    // also get relevant terms
    t->computeRelevantTerms(termSet);
    // also add them to the model 
    d_model->addRelevantTerms(termSet);
    Trace("model-builder") << "  CollectModelValues on theory: " << theoryId
                           << std::endl;
    // use the full set of relevant terms for all theories
    if (!t->collectModelValues(d_model, termSet))
    {
      Trace("model-builder")
          << "ModelManagerCentral: fail collect model values" << std::endl;
      return false;
    }
  }
  if (!collectModelBooleanVariables())
  {
    Trace("model-builder") << "ModelManagerCentral: fail Boolean variables"
                           << std::endl;
    return false;
  }

  return true;
}

bool ModelManagerCentral::isUsingRelevantTerms() const { return true; }

}  // namespace theory
}  // namespace CVC4
