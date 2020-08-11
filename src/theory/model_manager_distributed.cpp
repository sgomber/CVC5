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
    : d_te(te),
      d_logicInfo(te.getLogicInfo()),
      d_eem(eem),
      d_model(nullptr),
      d_modelBuilder(nullptr),
      d_modelBuilt(false),
      d_modelBuiltSuccess(false)
{
}

ModelManagerDistributed::~ModelManagerDistributed() {}

void ModelManagerDistributed::resetModel()
{
  d_modelBuilt = false;
  d_modelBuiltSuccess = false;
}

void ModelManagerDistributed::finishInit()
{
  const LogicInfo& logicInfo = d_te.getLogicInfo();
  // Initialize the model and model builder.
  if (logicInfo.isQuantified())
  {
    QuantifiersEngine* qe = d_te.getQuantifiersEngine();
    Assert(qe != nullptr);
    d_modelBuilder = qe->getModelBuilder();
    d_model = qe->getModel();
  }
  else
  {
    context::Context* u = d_te.getUserContext();
    d_alocModel.reset(
        new TheoryModel(u, "DefaultModel", options::assignFunctionValues()));
    d_model = d_alocModel.get();
  }

  // make the default builder, e.g. in the case that the quantifiers engine does
  // not have a model builder
  if (d_modelBuilder == nullptr)
  {
    d_alocModelBuilder.reset(new TheoryEngineModelBuilder(&d_te));
    d_modelBuilder = d_alocModelBuilder.get();
  }
}

bool ModelManagerDistributed::buildModel()
{
  if (d_modelBuilt)
  {
    // already computed
    return d_modelBuiltSuccess;
  }
  d_modelBuilt = true;
  d_modelBuiltSuccess = false;

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

void ModelManagerDistributed::postProcessModel(bool incomplete)
{
  if (!d_modelBuilt)
  {
    // model not built, nothing to do
    return;
  }
  Trace("model-builder") << "ModelManagerDistributed: post-process model..."
                         << std::endl;
  // model construction should always succeed unless lemmas were added
  AlwaysAssert(d_modelBuiltSuccess);
  if (!options::produceModels())
  {
    return;
  }
  // Do post-processing of model from the theories (used for THEORY_SEP
  // to construct heap model)
  for (TheoryId theoryId = theory::THEORY_FIRST; theoryId < theory::THEORY_LAST;
       ++theoryId)
  {
    Theory* t = d_te.theoryOf(theoryId);
    if (t == nullptr)
    {
      // theory not active, skip
      continue;
    }
    Trace("model-builder-debug")
        << "  PostProcessModel on theory: " << theoryId << std::endl;
    t->postProcessModel(d_model);
  }
  // also call the model builder's post-process model
  d_modelBuilder->postProcessModel(incomplete, d_model);
}

theory::TheoryModel* ModelManagerDistributed::getModel() { return d_model; }

bool ModelManagerDistributed::collectModelInfo()
{
  // Consult each active theory to get all relevant information
  // concerning the model.
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId < theory::THEORY_LAST; ++theoryId) {
    if (!d_logicInfo.isTheoryEnabled(theoryId))
    {
      // theory not active, skip
      continue;
    }
    Theory* t = d_te.theoryOf(theoryId);
    Trace("model-builder") << "  CollectModelInfo on theory: " << theoryId << std::endl;
    if (!t->collectModelInfo(d_model))
    {
      return false;
    }
  }
  Trace("model-builder") << "  CollectModelInfo boolean variables" << std::endl;
  // Get value of the Boolean variables
  prop::PropEngine* propEngine = d_te.getPropEngine();
  std::vector<TNode> boolVars;
  propEngine->getBooleanVariables(boolVars);
  std::vector<TNode>::iterator it, iend = boolVars.end();
  bool hasValue, value;
  for (it = boolVars.begin(); it != iend; ++it) {
    TNode var = *it;
    hasValue = propEngine->hasValue(var, value);
    // Should we assert that hasValue is true?
    if (!hasValue) {
      Trace("model-builder-assertions")
          << "    has no value : " << var << std::endl;
      value = false;
    }
    Trace("model-builder-assertions") << "(assert" << (value ? " " : " (not ") << var << (value ? ");" : "));") << std::endl;
    if (!d_model->assertPredicate(var, value))
    {
      return false;
    }
  }
  return true;
}

}  // namespace theory
}  // namespace CVC4
