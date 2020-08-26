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
#include "theory/output_channel.h"
#include "theory/theory_state.h"
#include "theory/trust_node.h"
#include "context/cdhashset.h"

namespace CVC4 {

class ProofNodeManager;

namespace theory {

class Theory;
namespace eq {
class EqualityEngine;
}

/**
 * The base class for inference manager.
 */
class InferManager
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
 public:
  /**
   * Constructor, note that state should be the official state of theory t.
   */
  InferManager(Theory& t, TheoryState& state);
  virtual ~InferManager() {}
  /**
   * Set equality engine, ee is a pointer to the official equality engine
   * of theory.
   */
  void setEqualityEngine(eq::EqualityEngine* ee);
  /**
   * Raise conflict, called when constants a and b merge. Sends the conflict
   * on the output channel corresponding to the equality engine's explanation
   * of (= a b). The proof equality engine (if it exists) will be used as the
   * proof generator.
   */
  void conflictEqConstantMerge(TNode a, TNode b);
  /**
   * Raise conflict conf (of any form), without proofs. This method should
   * only be called if there is not yet proof support in the given theory.
   */
  void conflict(TNode conf);
  /**
   * Raise trusted conflict tconf (of any form) where a proof generator has
   * been provided in a custom way.
   */
  void trustedConflict(TrustNode tconf);
  /**
   * T-propagate literal lit, possibly encountered by equality engine,
   * returns false if we are in conflict.
   */
  bool propagateLit(TNode lit);
  /**
   * Return an explanation for the literal represented by parameter n
   * (which was previously propagated by this theory).
   */
  virtual TrustNode explainLit(TNode lit);

  /** assert internal fact */
  void assertInternalFact(TNode atom, bool pol, TNode fact);

 protected:
  /** Explain conflict from constants merging in the equality engine */
  virtual TrustNode explainConflictEqConstantMerge(TNode a, TNode b);
  /** The theory object */
  Theory& d_theory;
  /** Reference to the state of theory */
  TheoryState& d_theoryState;
  /** Reference to the output channel of the theory */
  OutputChannel& d_out;
  /** Pointer to equality engine of the theory. */
  eq::EqualityEngine* d_ee;
  /** The proof node manager of the theory */
  ProofNodeManager* d_pnm;
  /**
   * The keep set of this class. This set is maintained to ensure that
   * facts and their explanations are ref-counted. Since facts and their
   * explanations are SAT-context-dependent, this set is also
   * SAT-context-dependent.
   */
  NodeSet d_keep;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__INFERENCE_MANAGER_H */
