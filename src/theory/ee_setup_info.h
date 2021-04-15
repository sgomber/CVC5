/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Setup information for an equality engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__EE_SETUP_INFO__H
#define CVC5__THEORY__EE_SETUP_INFO__H

#include <string>
#include <vector>

#include "expr/type_node.h"

namespace cvc5 {
namespace theory {

namespace eq {
class EqualityEngineNotify;
}

/**
 * Setup for a function kind. Sets up a call to EqualityEngine::addFunctionKind.
 */
struct EeSetupFunctionKind
{
  EeSetupFunctionKind(Kind k, bool isInt = false, bool isExtOp = false)
      : d_kind(k), d_isInterpreted(isInt), d_isExtOperator(isExtOp)
  {
  }
  /** The function kind */
  Kind d_kind;
  /** Whether its interpreted */
  bool d_isInterpreted;
  /** Whether its an external operator */
  bool d_isExtOperator;
};

/**
 * This is a helper class that encapsulates instructions for how a Theory
 * wishes to initialize and setup notifications with its official equality
 * engine, e.g. via a notification class (eq::EqualityEngineNotify).
 *
 * This includes (at a basic level) the arguments to the equality engine
 * constructor that theories may wish to modify. This information is determined
 * by the Theory during needsEqualityEngine.
 */
struct EeSetupInfo
{
  EeSetupInfo()
      : d_notify(nullptr), d_constantsAreTriggers(true), d_useMaster(false)
  {
  }
  /** The notification class of the theory */
  eq::EqualityEngineNotify* d_notify;
  /** The name of the equality engine */
  std::string d_name;
  /** Constants are triggers */
  bool d_constantsAreTriggers;
  /** The set of kinds to do congruence over */
  std::vector<EeSetupFunctionKind> d_functionKinds;
  //-------------------------- fine grained notifications
  /** The TypeNode kinds to notify on eqNotifyNewClass */
  std::vector<Kind> d_notifyNewEqClassTypeKinds;
  /** The Node kinds to notify on eqNotifyNewClass */
  std::vector<Kind> d_notifyNewEqClassKinds;
  /** Specific types to notify on eqNotifyNewClass. */
  std::vector<TypeNode> d_notifyNewEqClassTypes;
  /** The TypeNode kinds to notify on eqNotifyMerge */
  std::vector<Kind> d_notifyMergeTypeKinds;
  /** Specific types to notify on eqNotifyMerge. */
  std::vector<TypeNode> d_notifyMergeTypes;
  /** The TypeNode kinds to notify on eqNotifyDisequal */
  std::vector<Kind> d_notifyDisequalTypeKinds;
  /** Specific types to notify on eqNotifyDisequal. */
  std::vector<TypeNode> d_notifyDisequalTypes;
  //-------------------------- end fine grained notifications
  /** Does it need notifications when equivalence classes are created? */
  bool needsNotifyNewEqClass() const
  {
    return !d_notifyNewEqClassTypeKinds.empty()
           || !d_notifyNewEqClassKinds.empty()
           || !d_notifyNewEqClassTypes.empty();
  }
  /** Does it need notifications when equivalence classes are merged? */
  bool needsNotifyMerge() const
  {
    return !d_notifyMergeTypeKinds.empty() || !d_notifyMergeTypes.empty();
  }
  /** Does it need notifications when disequalities are generated? */
  bool needsNotifyDisequal() const
  {
    return !d_notifyDisequalTypeKinds.empty() || !d_notifyDisequalTypes.empty();
  }
  /**
   * Whether we want our state to use the master equality engine. This should
   * be true exclusively for the theory of quantifiers.
   */
  bool d_useMaster;
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__EE_SETUP_INFO__H */
