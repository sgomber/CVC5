/*********************                                                        */
/*! \file model_manager_central.h
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

#include "cvc4_private.h"

#ifndef CVC4__THEORY__MODEL_MANAGER_CENTRAL__H
#define CVC4__THEORY__MODEL_MANAGER_CENTRAL__H

#include <map>
#include <memory>

#include "theory/ee_manager_central.h"
#include "theory/model_manager.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Manager for building models in a central architecture.
 */
class ModelManagerCentral : public ModelManager
{
 public:
  ModelManagerCentral(TheoryEngine& te, EqEngineManagerCentral& eem);
  ~ModelManagerCentral();
  /**
   * Prepare model. This method returns true if the model has been successfully
   * prepared.
   *
   * In contrast to other model managers, this method pushes a SAT context
   * to ensure the state of the system is tracked before attempting to build
   * the model. It additionally tracks relevant terms in the model via
   * calls to TheoryModel::addRelevantTerms.
   *
   * If this method returns false, then we pop the SAT context and the system
   * returns to its original state. If this method returns true, then the SAT
   * context push remains open. It is popped again on finishBuildModel if
   * we fail to build the model.
   */
  bool prepareModel() override;
  /**
   * Finish build model, which calls the theory model builder to assign values
   * to all equivalence classes. This should be run after prepareModel.
   *
   * This class overrides the behavior of finishBuildModel by:
   * (1) Indicating to the model builder that we wish to use relevant terms
   * in the equality engine of the model (which is the central equality engine).
   * The purpose of this is to only consider terms that have been marked
   * relevant by a theory. We do this via an explicit set since it is not
   * possible to remove terms from the equality engine.
   * (2) Popping a SAT context if we are not successful.
   */
  bool finishBuildModel() const override;

 private:
  /**
   * Central equality engine manager.
   */
  EqEngineManagerCentral& d_eem;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__MODEL_MANAGER_CENTRAL__H */
