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

#include "theory/model_manager.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Manager for building models in a distributed architecture.
 */
class ModelManagerCentral : public ModelManager
{
 public:
  ModelManagerCentral(TheoryEngine& te);
  ~ModelManagerCentral();
  /** Prepare model */
  bool prepareModel() override;
  /** is using relevant terms? */
  bool isUsingRelevantTerms() const override;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__MODEL_MANAGER_CENTRAL__H */
