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
#include "theory/theory_id.h"
#include "theory/theory_state.h"
#include "theory/trust_node.h"

namespace CVC4 {

class ProofNodeManager;

namespace theory {

namespace eq {
class EqualityEngine;
}

/**
 * The base class for inference manager.
 */
class InferManager
{
 public:
  InferManager(TheoryId tid,
               TheoryState& state,
               OutputChannel& out,
               ProofNodeManager* pnm);
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
   * Raise conflict conf (of any form), without proofs.
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
  bool propagate(TNode lit);
  /**
   * Return an explanation for the literal represented by parameter n
   * (which was previously propagated by this theory).
   */
  virtual TrustNode explain(TNode lit);

 protected:
  /** Make trusted conflict */
  virtual TrustNode mkTrustedConflictEqConstantMerge(TNode a, TNode b);
  /** Make trusted conflict */
  virtual TrustNode mkTrustedConflict(TNode conf);
  /**
   * Explain literal l, return conjunction.
   */
  Node mkExplain(TNode literal) const;
  /**
   * Explain literal l, add conjuncts to assumptions vector instead of making
   * the node corresponding to their conjunction.
   */
  void explain(TNode literal, std::vector<TNode>& assumptions) const;
  /** The identifier */
  TheoryId d_theoryId;
  /** Reference to the state of theory */
  TheoryState& d_state;
  /** Reference to the output channel of the theory */
  OutputChannel& d_out;
  /** Pointer to equality engine of the theory. */
  eq::EqualityEngine* d_ee;
  /** The proof node manager */
  ProofNodeManager* d_pnm;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__INFERENCE_MANAGER_H */
