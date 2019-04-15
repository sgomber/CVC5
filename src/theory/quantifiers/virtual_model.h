/*********************                                                        */
/*! \file formula_evaluator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Virtual model utility.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__VIRTUAL_MODEL_H
#define __CVC4__THEORY__QUANTIFIERS__VIRTUAL_MODEL_H

#include <map>
#include <vector>
#include "expr/node.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"
#include "theory/valuation.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Virtual model
 */
class VirtualModel : public QuantifiersUtil
{
 public:
  VirtualModel(QuantifiersEngine* qe);
  /** reset */
  bool reset(Theory::Effort e) override;
  /* Called for new quantifiers */
  void registerQuantifier(Node q) override;
  /** Identify this module*/
  std::string identify() const override { return "VirtualModel"; }
  /** register assertion */
  bool registerAssertion(Node ilem);
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
  int evaluate(Node n, bool useEntailment = false);
  /**
   * Evaluate, starting with a custom set of assumptions instead of using
   * d_ecache. The values in assumptions can be thought of as overriding the
   * model values for the given formula.
   */
  int evaluateWithAssumptions(Node n,
                              std::map<Node, int>& assumptions,
                              bool useEntailment = false);
  /** ensure value */
  bool ensureValue(Node n,
                   bool isTrue,
                   std::map<Node, int>& setAssumps,
                   bool allowDec = false,
                   bool useEntailment = true);

 private:
  /** quantifiers engine */
  QuantifiersEngine* d_qe;
  /** term database of quantifiers engine */
  TermDb* d_tdb;
  /** valuation */
  Valuation& d_valuation;
  /** cache */
  std::map<Node, int> d_ecache;
  /**
   * evaluate n given cache assumptions.
   *
   * ucache stores the nodes whose return value is 0. We only cache the value of
   * nodes in assumptions whose value is known. This is useful if we want to
   * decide on the truth value of literals later.
   *
   * if useEntailment is true, we use the entailmentCheck method of d_tdb on
   * literals whose value is unknown to determine their value.
   */
  int evaluateInternal(Node n,
                       std::map<Node, int>& assumptions,
                       std::unordered_set<Node, NodeHashFunction>& ucache,
                       bool useEntailment);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__IEX_EVALUATOR_H */
