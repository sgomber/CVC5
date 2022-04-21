/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inst evaluator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_EVALUATOR_H
#define CVC5__THEORY__QUANTIFIERS__INST_EVALUATOR_H

#include <vector>

#include "expr/node.h"
#include "expr/node_converter.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Inst evaluator
 *
 * Incrementally maintains the state of the rewritten form of the quantified
 * formula.
 */
class InstEvaluator : public NodeConverter
{
public:
  InstEvaluator(Node q);
  /** Return false if we are infeasible */
  bool initialize();
  /** Return false if we are infeasible */
  bool push(TNode v, TNode s);
  /** */
  void pop();
protected:
  /** Push internal */
  bool convertAndPush(Node body);
  /** Should we traverse n? */
  bool shouldTraverse(Node n) override;
  /** Post convert */
  Node postConvert(Node n) override;
  /** 
   * Evaluate internal
   * 
   * This method should return the evaluation of n { v -> s }, and set
   * the feasible flag to false if the instantiation is infeasible.
   * 
   * It may be the case that v and s are null, in which case we are
   * initializing.
   */
  virtual Node evaluateInternal(Node n, TNode v, TNode s, bool& feasible) = 0;
  /** The quantified formula */
  Node d_quant;
  /** The stack of the evaluated body */
  std::vector<Node> d_evalBody;
  /** The current substitution */
  TNode d_currVar;
  TNode d_currSubs;
  /** currently feasible */
  bool d_currFeasible;
};


}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__INST_EVALUATOR_H */
