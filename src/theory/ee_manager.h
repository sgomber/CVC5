/*********************                                                        */
/*! \file ee_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for management of equality engines.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__EE_MANAGER__H
#define CVC4__THEORY__EE_MANAGER__H

#include <map>
#include <memory>

#include "theory/ee_setup_info.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {

/**
 * This is (theory-agnostic) information associated with the management of
 * an equality engine for a single theory. This information is maintained
 * by the manager class below.
 *
 * Currently, this simply is the equality engine itself, for memory
 * management purposes.
 */
struct EeTheoryInfo
{
  EeTheoryInfo() : d_usedEe(nullptr) {}
  /** Equality engine that is used (if it exists) */
  eq::EqualityEngine* d_usedEe;
  /** Equality engine allocated specifically for this theory (if it exists) */
  std::unique_ptr<eq::EqualityEngine> d_allocEe;
};

/** Virtual base class for equality engine managers */
class EqEngineManager
{
 public:
  virtual ~EqEngineManager() {}
  /**
   * Initialize theories, called during TheoryEngine::finishInit after theory
   * objects have been created but prior to their final initialization. This
   * sets up equality engines for all theories.
   *
   * This method is context-independent, and is applied once during
   * the lifetime of TheoryEngine (during finishInit).
   */
  virtual void initializeTheories() = 0;
  /**
   * Initialize model, called during TheoryEngine::finishInit after the model
   * manager has been initialized.
   *
   * This method is context-independent, and is applied once during
   * the lifetime of TheoryEngine (during finishInit).
   */
  virtual void initializeModel(TheoryModel* m) = 0;
  /**
   * Get the equality engine theory information for theory with the given id.
   */
  const EeTheoryInfo* getEeTheoryInfo(TheoryId tid) const;
  /**
   * Get the core equality engine, which is the equality engine that the
   * quantifiers engine should use. This corresponds to the master equality
   * engine if eeMode is distributed, or the central equality engine if eeMode
   * is central.
   */
  virtual eq::EqualityEngine* getCoreEqualityEngine() = 0;
  
  //---------------------------- interaction with CombinationEngine
  /**
   * Get the equality status of a and b.
   *
   * This method is used by theories during solving ...
   */
  virtual EqualityStatus getEqualityStatus(TNode a, TNode b)  = 0;
  /**
   * Explain literal, which returns a conjunction of literals that that entail
   * the given one.
   *
   * This method is used by TheoryEngine when it wants an explanation of a
   * propagation that was made by the shared terms database.
   */
  virtual TrustNode explainShared(TNode literal) const = 0;
  /**
   * Assert equality to the shared terms database.
   *
   * This method is called by TheoryEngine when a fact has been marked to
   * send to THEORY_BUILTIN, meaning that shared terms database should
   * maintain this fact. This is the case when ...
   */
  virtual void assertSharedEquality(TNode equality, bool polarity, TNode reason) = 0;
  //---------------------------- end interaction with CombinationEngine
 protected:
  /** Information related to the equality engine, per theory. */
  std::map<TheoryId, EeTheoryInfo> d_einfo;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__EE_MANAGER__H */
