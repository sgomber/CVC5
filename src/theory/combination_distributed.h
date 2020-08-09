/*********************                                                        */
/*! \file combination_distributed.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for theory combination.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__COMBINATION_DISTRIBUTED__H
#define CVC4__THEORY__COMBINATION_DISTRIBUTED__H

#include <map>
#include <memory>

#include "theory/shared_terms_database.h"
#include "theory/ee_manager_distributed.h"
#include "theory/model_manager_distributed.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Manager for doing theory combination in a distributed architecture.
 */
class CombinationDistributed
{
 public:
  CombinationDistributed(TheoryEngine& te);
  ~CombinationDistributed();
  /** Finish initialization */
  void finishInit();
  /** Combine theories */
  void combineTheories();
  //-------------------------- model
  /** reset model */
  void resetModel();
  /** Build model */
  bool buildModel();
  /** Post process model */
  void postProcessModel(bool incomplete);
  /** Get model */
  theory::TheoryModel* getModel();
  //-------------------------- end model
 private:
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /**
   * The database of shared terms.
   */
  SharedTermsDatabase d_sharedTerms;

  /**
   * The distributed equality manager. This class is responsible for
   * configuring the theories of this class for handling equalties
   * in a "distributed" fashion, i.e. each theory creates its own
   * instance of an equality engine. These equality engines are managed
   * by this class.
   */
  std::unique_ptr<theory::EqEngineManagerDistributed> d_eeDistributed;

  /** The model manager */
  std::unique_ptr<theory::ModelManagerDistributed> d_mDistributed;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__COMBINATION_DISTRIBUTED__H */
