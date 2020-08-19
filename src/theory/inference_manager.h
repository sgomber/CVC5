/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An inference manager for Theory
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__INFERENCE_MANAGER_H
#define CVC4__THEORY__INFERENCE_MANAGER_H

#include "expr/node.h"
#include "theory/theory_state.h"
#include "theory/trust_node.h"
#include "theory/output_channel.h"

namespace CVC4 {
namespace theory {

namespace eq {
class EqualityEngine;
}

/**
 * The base class for inference manager.
 */
class InferenceManager
{
 public:
  InferenceManager(TheoryState& state, OutputChannel& out);
  virtual ~InferenceManager() {}
  /**
   * Set equality engine, ee is a pointer to the official equality engine
   * of theory.
   */
  void setEqualityEngine(eq::EqualityEngine* ee);
  /** 
   * Raise conflict, called when constants a and b merge. Sends the conflict
   * on the output channel corresponding to the equality engine's explanation
   * of (= a b).
   */
  void conflictConstantEq(TNode a, TNode b);
  /** Raise conflict conf */
  void conflict(TNode conf);
  /** Raise trusted conflict conf */
  void trustedConflict(TrustNode tconf);
  /**
   * T-propagate literal lit encountered by equality engine,
   */
  bool propagate(TNode lit);
 protected:
  /** Reference to the state of theory */
  TheoryState& d_state;
  /** Reference to the output channel of the theory */
  OutputChannel& d_out;
  /** Pointer to equality engine of the theory. */
  eq::EqualityEngine* d_ee;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__INFERENCE_MANAGER_H */
