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
  /** evaluate */
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
   * Set that instantiation lemma inst contains this literal.
   *
   * If isPropagating is true, then it is possible that inst may propagate
   * this literal. This impacts whether we add inst to the vector d_insts below.
   */
  void addInstExplanation(Node inst, Node origLit, bool isPropagating = true);
  /**
   * Set that instantiation lemma inst currently propagates the literal of this
   * object. This is called by InstExplainDb.
   *
   * inst should be an instantiation lemma occurring as an argument to a
   * previous call to addInstExplanation.
   */
  void setPropagating(Node inst);
  /**
   * The list of current instantiation lemmas that explain this literal.
   * These are formulas are a subset of d_insts.
   */
  std::vector<Node> d_curr_insts;
  /** The list of instantiation lemmas that may propagate d_this. */
  std::vector<Node> d_insts;
  /** get original lit for instantiation */
  Node getOriginalLit(Node inst) const;

 private:
  /** The literal of this object. */
  Node d_this;
  /** the original literal, for each instantiation */
  std::map<Node, Node> d_orig_ilit;
  std::map<Node, Node> d_orig_lit;
};

class InstExplainInst
{
 public:
  /** initialize */
  void initialize(Node inst, Node q, const std::vector<Node>& ts);
  /** propagate */
  void propagate(IeEvaluator& v, std::vector<Node>& lits);
  /** get substitution */
  Node getSubstitution(unsigned index) const;
  /** get explanation */
  Node getExplanationFor(Node lit);
  /** get quantified formula */
  Node getQuantifiedFormula() const;

 private:
  /** the instantiation lemma */
  Node d_this;
  /** the quantified formula */
  Node d_quant;
  /** the substitution for this instantiation */
  std::vector<Node> d_terms;
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
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_H */
