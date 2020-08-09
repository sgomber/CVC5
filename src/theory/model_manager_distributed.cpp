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

#include "theory/theory_engine.h"
#include "options/theory_options.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {

ModelManagerDistributed::ModelManagerDistributed(TheoryEngine& te, EqEngineManagerDistributed& eem) : d_te(te), d_eem(eem), d_model(nullptr), d_modelBuilder(nullptr)
{
  
}

ModelManagerDistributed::~ModelManagerDistributed()
{
  
}

void ModelManagerDistributed::resetModel()
{
  d_model->reset();
  // push/pop to clear the equality engine of the model
  context::Context* meec = d_eem.getModelEqualityEngineContext();
  meec->pop();
  meec->push();
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
  } else {
    context::Context* u = d_te.getUserContext();
    d_alocModel.reset(new TheoryModel(
        u, "DefaultModel", options::assignFunctionValues()));
    d_model = d_alocModel.get();
  }

  //make the default builder, e.g. in the case that the quantifiers engine does not have a model builder
  if( d_modelBuilder==nullptr ){
    d_alocModelBuilder.reset(new TheoryEngineModelBuilder(&d_te));
    d_modelBuilder = d_alocModelBuilder.get();
  }
  
  // initialize equality engine of model
  d_eem.initializeModel(d_model);
}

bool ModelManagerDistributed::buildModel()
{
  if (d_model->isBuilt())
  {
    return true;
  }
  // need this???
  resetModel();
  return d_modelBuilder->buildModel(d_model);
}

void ModelManagerDistributed::postProcessModel(bool incomplete)
{
  if (!d_model->isBuilt())
  {
    // model not built, nothing to do
    return;
  }
  // model construction should always succeed unless lemmas were added
  AlwaysAssert(d_model->isBuiltSuccess());
  if (!options::produceModels())
  {
    return;
  }
  // Do post-processing of model from the theories (used for THEORY_SEP
  // to construct heap model)
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId < theory::THEORY_LAST; ++theoryId)
  {
    Theory* t = d_te.theoryOf(theoryId);
    if (t == nullptr)
    {
      // theory not active, skip
      continue;
    }
    Trace("model-builder-debug") << "  PostProcessModel on theory: " << theoryId << std::endl;
    t->postProcessModel( d_model );
  }
  // also call the model builder's post-process model
  d_modelBuilder->postProcessModel(incomplete, d_model);
}

theory::TheoryModel* ModelManagerDistributed::getModel()
{
  return d_model;
}

}  // namespace theory
}  // namespace CVC4
