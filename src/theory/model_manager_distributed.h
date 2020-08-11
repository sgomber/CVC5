/*********************                                                        */
/*! \file ee_manager_distributed.h
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

#include "cvc4_private.h"

#ifndef CVC4__THEORY__MODEL_MANAGER_DISTRIBUTED__H
#define CVC4__THEORY__MODEL_MANAGER_DISTRIBUTED__H

#include <map>
#include <memory>

#include "theory/ee_manager_distributed.h"
#include "theory/theory_model.h"
#include "theory/theory_model_builder.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Manager for building models in a distributed architecture.
 */
class ModelManagerDistributed
{
 public:
  ModelManagerDistributed(TheoryEngine& te, EqEngineManagerDistributed& eem);
  ~ModelManagerDistributed();
  /** reset model */
  void resetModel();
  /** finish init */
  void finishInit();
  /** Build model */
  bool buildModel();
  /** Post process model */
  void postProcessModel(bool incomplete);
  /** Get model */
  theory::TheoryModel* getModel();

  /** Collect model info */
  bool collectModelInfo();
 private:
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** Logic info of theory engine (cached) */
  const LogicInfo& d_logicInfo;
  /** Reference to the equality engine manager */
  EqEngineManagerDistributed& d_eem;
  /** The model object we are using */
  theory::TheoryModel* d_model;
  /** The model object we have allocated (if one exists) */
  std::unique_ptr<theory::TheoryModel> d_alocModel;
  /** The model builder object we are using */
  theory::TheoryEngineModelBuilder* d_modelBuilder;
  /** The model builder object we have allocated (if one exists) */
  std::unique_ptr<theory::TheoryEngineModelBuilder> d_alocModelBuilder;
  /** whether we have tried to build this model in the current context */
  bool d_modelBuilt;
  /** whether this model has been built successfully */
  bool d_modelBuiltSuccess;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__MODEL_MANAGER_DISTRIBUTED__H */
