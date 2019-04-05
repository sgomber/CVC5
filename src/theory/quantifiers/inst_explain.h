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

 private:
  /** valuation */
  Valuation& d_valuation;
  /** cache */
  std::map<Node, int> d_ecache;
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
  void propagate(IeEvaluator& v, std::vector<Node>& lits, std::vector< Node >& olits);
  /** reverse propagate 
   * 
   * This returns a set of literals that are current the reason for propagating
   * the literal olit.
   */
  bool revPropagate(IeEvaluator& v, Node olit, std::vector<Node>& lits, std::vector< Node >& olits);
  
  /** get explanation */
  Node getExplanationFor(Node lit);
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
   * Maps literals to their explanation via this instantiation.
   * Let C[L] be a clause containing literal L. The explanation for C with
   * respect to L is ~C[false]. For example:
   *    ~(forall x. P(x) V Q(x)) V P(c) V Q(c)
   * the explanation for ~forall x. P(x) V P(c) V Q(c) with respect to P(c) is
   *   (forall x. P(x)) ^ ~Q(c)
   * which notice suffices to show that P(c) much be true.
   * We map L to ~C[false] in this vector.
   */
  std::map<Node, Node> d_lit_to_exp;
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
  void propagateInternal(Node n, Node on, IeEvaluator& v, std::vector<Node>& lits, std::vector< Node >& olits);

  /** get the propagating literals for n
   *
   * If this method returns true, then lits contains a set of literals over the
   * atoms of n that propositionally entail n and are true in the current SAT
   * context.
   * If this method returns false, then n is not true in the current SAT
   * context.
   *
   * The processed nodes are cached in cache.
   */
  bool revPropagateInternal(TNode n, TNode on, bool pol, IeEvaluator& v,std::map<Node, std::map< bool, bool > >& cache, std::vector<Node>& lits, std::vector< Node >& olits);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_H */
