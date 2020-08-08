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
 ** \brief Management of a distributed approach for equality sharing.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__EE_MANAGER_DISTRIBUTED__H
#define CVC4__THEORY__EE_MANAGER_DISTRIBUTED__H

#include <memory>
#include <map>

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
  
class TheoryEngine;

namespace theory {

class EeTheoryInfo
{
public:
  
  /** The equality engine allocated by this theory (if it exists) */
  std::unique_ptr<eq::EqualityEngine> d_allocEe;
};
  
class EqEngineManagerDistributed
{
public:
  EqEngineManagerDistributed(TheoryEngine& te);
  ~EqEngineManagerDistributed();
  /** finish initialize */
  void finishInit();
  /** get the master equality engine */
  eq::EqualityEngine* getMasterEqualityEngine();
private:
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** Pointer to quantifiers engine of d_te */
  QuantifiersEngine * d_quantEngine;
  /** notify class for master equality engine */
  class MasterNotifyClass : public theory::eq::EqualityEngineNotify {
    QuantifiersEngine * d_quantEngine;
  public:
    MasterNotifyClass(QuantifiersEngine * qe): d_quantEngine(qe) {}
    /**
     * Called when a new equivalence class is created in the master equality
     * engine.
     */
    void eqNotifyNewClass(TNode t) override;
  };
  std::unique_ptr<MasterNotifyClass> d_masterEENotify;
  /**
   * Master equality engine, to share with theories.
   */
  std::unique_ptr<eq::EqualityEngine> d_masterEqualityEngine;
  /**
   * The equality engines that have been allocated for each theory
   */
  std::map<TheoryId, EeTheoryInfo> d_einfo;
};
  
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__EE_MANAGER_DISTRIBUTED__H */
