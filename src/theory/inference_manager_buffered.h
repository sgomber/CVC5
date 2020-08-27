/*********************                                                        */
/*! \file inference_manager_buffered.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A buffered inference manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__INFERENCE_MANAGER_BUFFERED_H
#define CVC4__THEORY__INFERENCE_MANAGER_BUFFERED_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "theory/theory_inference_manager.h"

namespace CVC4 {
namespace theory {

/**
 * The datatypes inference manager.
 */
class InferenceManagerBuffered : public TheoryInferenceManager
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  InferenceManagerBuffered(Theory& t,
                           TheoryState& state,
                           ProofNodeManager* pnm);
  ~InferenceManagerBuffered() {}
  /**
   * Have we processed an inference during this call to check? In particular,
   * this returns true if we have a pending fact or lemma, or have encountered
   * a conflict.
   */
  bool hasProcessed() const;
  /** Do we have a pending fact to add as an internal fact to the equality
   * engine? */
  bool hasPendingFact() const;
  /** Do we have a pending lemma to send on the output channel? */
  bool hasPendingLemma() const;
  /** Add pending lemma */
  void addPendingLemma(Node lem, LemmaProperty p = LemmaProperty::NONE);
  /** Add pending lemma */
  void addPendingFact(Node fact, Node exp, bool asLemma = false);
  /** Do pending facts
   *
   * This method asserts pending facts (d_pending) with explanations
   * (d_pendingExp) to the equality engine of the theory via calls
   * to assertInternalFact.
   *
   * It terminates early if a conflict is encountered, for instance, by
   * equality reasoning within the equality engine.
   *
   * Regardless of whether a conflict is encountered, the vector d_pending
   * and map d_pendingExp are cleared.
   */
  void doPendingFacts();
  /** Do pending lemmas
   *
   * This method flushes all pending lemmas (d_pendingLem) to the output
   * channel of the theory.
   *
   * Like doPendingFacts, this function will terminate early if a conflict
   * has already been encountered by the theory of strings. The vector
   * d_pending_lem is cleared regardless of whether a conflict is discovered.
   *
   * Notice that as a result of the above design, some lemmas may be "dropped"
   * if a conflict is discovered in between when a lemma is added to the
   * pending vector of this class (via a sendInference call). Lemmas
   * e.g. those that are required for initialization should not be sent via
   * this class, since they should never be dropped.
   */
  void doPendingLemmas();
 protected:
  /**
   * Called when a pending fact is about to be sent, return true if the fact
   * was processed separately (i.e. it should not be asserted).
   */
  virtual bool preNotifyPendingFact(TNode atom, bool pol, TNode fact);
  /**
   * Called when a pending lemma is about to be sent, return true if the lemma
   * was processed separately (i.e. it should not be asserted). A common
   * usage of this method would be to check whether we have already sent this
   * lemma in the current user context.
   */
  virtual bool preNotifyPendingLemma(TNode lem, LemmaProperty p);
  /** A set of pending lemmas */
  std::vector<std::pair<Node, LemmaProperty>> d_pendingLem;
  /** A set of pending facts, paired with their explanations */
  std::vector<std::pair<Node, Node>> d_pendingFact;
};

}  // namespace theory
}  // namespace CVC4

#endif
