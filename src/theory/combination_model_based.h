/*********************                                                        */
/*! \file combination_model_based.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a care graph based approach for theory combination.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__COMBINATION_MODEL_BASED__H
#define CVC4__THEORY__COMBINATION_MODEL_BASED__H

#include <map>
#include <memory>

#include "theory/combination_engine.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Manager for doing theory combination using a model-based approach. This is
 * typically done via a central equalty engine architecture.
 */
class CombinationModelBased : public CombinationEngine
{
 public:
  CombinationModelBased(TheoryEngine& te,
                        const std::vector<Theory*>& paraTheories);
  ~CombinationModelBased();

  /** Build model (a no-op) */
  bool buildModel() override;
  /**
   * Combine theories using model building.
   */
  void combineTheories() override;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__COMBINATION_MODEL_BASED__H */
