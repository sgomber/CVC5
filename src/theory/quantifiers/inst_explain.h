/*********************                                                        */
/*! \file inst_explain.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Instantiate explain utility
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_H
#define __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_H

#include <map>
#include <vector>
#include "expr/node.h"
#include "theory/valuation.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class IeEvaluator
{
 public:
  IeEvaluator(Valuation& v) : d_valuation(v) {}
  /** reset */
  void reset();
  /** evaluate
   *
   * Returns the value of n in the current SAT context where
   * 1 : n is true in the SAT context,
   * -1 : n is false in the SAT context,
   * 0 : the value of n is unknown in the current SAT context.
   *
   * Notice that n may contain literals that do not have values in the SAT
   * context. The value of n can still be determined in some cases in the
   * case these literals are irrelevant.
   */
  int evaluate(Node n);
  /**
   * Evaluate, starting with a custom set of assumptions instead of using
   * d_ecache. The values in assumptions can be thought of as overriding the
   * model values for the given formula.
   */
  int evaluateWithAssumptions(Node, std::map<Node, int>& assumptions);

 private:
  /** valuation */
  Valuation& d_valuation;
  /** cache */
  std::map<Node, int> d_ecache;
  /** evaluate n given cache assumptions. */
  int evaluateInternal(Node n, std::map<Node, int>& assumptions);
};

/** instantiation explain literal
 *
 * This class manages all instantiation lemma explanations for a single ground
 * literal L. In particular, it stores all instantiation lemmas that contain
 * and may propagate L.
 */
class InstExplainLit
{
 public:
  InstExplainLit() {}
  /** Initialize this object for literal lit. */
  void initialize(Node lit);
  /** Reset, called at the beginning of instantiation rounds. */
  void reset();
  /**
   * Set that instantiation lemma inst may propagate thils literal.
   */
  void addInstExplanation(Node inst);
  /**
   * Set that instantiation lemma inst currently propagates the literal of this
   * object. This is called by InstExplainDb.
   *
   * inst should be an instantiation lemma occurring as an argument to a
   * previous call to addInstExplanation.
   */
  void setPropagating(Node inst, Node olit);
  /**
   * The list of current instantiation lemmas that explain this literal.
   * These are formulas are a subset of d_insts.
   */
  std::vector<Node> d_curr_insts;
  /**
   * Original literals  FIXME
   */
  std::vector<Node> d_curr_olits;
  /** The list of instantiation lemmas that may propagate d_this. */
  std::vector<Node> d_insts;

 private:
  /** The literal of this object. */
  Node d_this;
};

class InstExplainInst
{
 public:
  /** initialize
   *
   * inst: the (rewritten) instantiation lemma,
   * body: the substituted form of the body (alpha-equivalent to q[1]),
   * q: the quantified formula,
   * ts: the terms we substituted into q[1] to obtain body.
   */
  void initialize(Node inst, Node body, Node q, const std::vector<Node>& ts);
  /** propagate
   *
   * This returns a set of ground literals lits that are currently propagated by
   * this instantiation lemma. For each lits[i], olits[i] is corresponding
   * formula in the body of q at the same position. This is motivated by the
   * follwoing observation: a ground literal may occur in multiple positions in
   * an instantiation lemma. For example, body of the instantiation lemma
   *    forall x. P( x, y ) V P( a, x ) for { x -> a, y -> a }
   * has two occurrences of P( a, a ). It is important to track this
   * information, since it impacts how certain explanations are constructed.
   */
  void propagate(IeEvaluator& v,
                 std::vector<Node>& lits,
                 std::vector<Node>& olits);
  /** reverse propagate
   *
   * This returns a set of literals lits (and their generalizations, in olits)
   * that are current the reason for the instantiation lemma of this class
   * propagating the ground form of literal olit.
   *
   * For example, given instantiation lemma:
   *    forall x. P( x ) V Q( x ) => P( a ) V Q( a )
   * If forall x. P( x ) V Q( x ), and ~Q( a ) are asserted, then this
   * instantiation lemma propagates P( a ). The generalized form of P( a ) is
   * the formula at the same position in the quantified formula: P( x ).
   * Calling this method on olit will return true with:
   *   lits = { forall x. P( x ) V Q( x ), ~Q( a ) }
   *   olits = { forall x. P( x ) V Q( x ), ~Q( x ) }
   * Notice that the quantified formula itself appears in both lits/olits.
   *
   * We compute lits and olits based on the following observation:
   * If the instantiation lemma above (call it C) propagates P( a ), then
   * C { P( a ) -> false } must evaluate to false in the current context.
   * Thus, we compute lits and olits by justifying why C { P( a ) -> false }
   * evaluates to false in the current context, as witnessed by v.
   */
  bool justify(IeEvaluator& v,
               Node lit,
               Node olit,
               std::vector<Node>& lits,
               std::vector<Node>& olits);

  /** get quantified formula */
  Node getQuantifiedFormula() const;
  /** the substitution for this instantiation */
  std::vector<Node> d_terms;

 private:
  /** the (rewritten) instantiation lemma */
  Node d_this;
  /**
   * The instantiation (non-rewritten) body. This must be matchable with
   * d_quant, since we do parallel traversals of this node with the body of
   * d_quant.
   */
  Node d_body;
  /** the quantified formula */
  Node d_quant;
  /**
   * FIXME move doc
   * Maps literals to their explanation via this instantiation.
   * Let C[L] be a clause containing literal L. The explanation for L with
   * respect to C is C[false]. For example:
   *    ~(forall x. P(x) V Q(x)) V P(c) V Q(c)
   * the explanation for P(c) with respect to this instantiation lemma is
   *   false V Q(c)
   * The negation of this formula plus the quantified formula and the original
   * instantiation lemma suffice to show that P(c) must be true.
   * We map L to C[false] in this vector.
   */

  /** propagate internal
   *
   * n is a formula that is matchable with on, and holds in the current SAT
   * context (as witnessable by the evaluator utility v).
   *
   * This function does a parallel traversal of n and on and adds a set of
   * literals to lits such that each L can be inferred by Boolean propagation.
   * That is, assuming a model M assigning truth values to the atoms of n,
   * we add L to lits if it is the case that the propositional entailment holds:
   *   n, ( M \ atom(L) ) |= L
   * We additionally add the (original) versions of lits to olits.
   */
  void propagateInternal(Node n,
                         Node on,
                         IeEvaluator& v,
                         std::vector<Node>& lits,
                         std::vector<Node>& olits);

  /** get the propagating literals for n
   *
   * This method computes a justification for a ground formula n, while
   * tracking its generalized form on.
   *
   * If this method returns true, then lits contains a set of literals over the
   * atoms of n that propositionally entail ( pol ? n : ~n ) and are true in the
   * current SAT context. If this method returns false, then ( pol ? n : ~n ) is
   * not entailed to be true in the current SAT context.
   *
   * We do a parallel traversal of n and on, where on is matchable with n and
   * add the formulas into olits at the same position as those added to lits.
   *
   * The processed nodes are cached in cache.
   */
  bool justifyInternal(TNode n,
                       TNode on,
                       bool pol,
                       Node olitProp,
                       IeEvaluator& v,
                       std::map<Node, int>& assumptions,
                       std::map<Node, std::map<bool, bool> >& cache,
                       std::vector<Node>& lits,
                       std::vector<Node>& olits);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_H */
