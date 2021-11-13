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
 * Info per quantified formula in CCFV.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__QUANT_INFO_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__QUANT_INFO_H

#include <map>

#include "context/cdo.h"
#include "expr/node.h"
#include "expr/term_canonize.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

class QuantInfo
{
 public:
  QuantInfo(context::Context* c);
  /**
   * Initialize, called once.
   */
  void initialize(TNode q, expr::TermCanonize& tc);
  /**
   * Reset round, called once per full effort check
   */
  void resetRound();
  /**
   * Get next matcher from the list, increment the index for which matcher
   * we are considering.
   */
  TNode getNextMatcher();
  /**
   * Get match constraints.
   *
   */
  const std::map<TNode, std::vector<Node>>& getMatchConstraints(
      bool isEq) const;

 private:
  /**
   * Process matching requirement for subterm cur which is a disjunct in the
   * quantified formula of this class.
   */
  void processMatchRequirement(TNode cur, std::vector<TNode>& visit);
  /** Add match term that must be (dis)equal from eqc */
  void addMatchTermReq(TNode t, Node eqc, bool isEq);
  /** Same as above, with requirement */
  void addMatchTerm(TNode t);
  //------------------- static
  /** The quantified formula */
  Node d_quant;
  /** Canonical form of body */
  Node d_canonBody;
  /**
   * List of canonical variables corresponding to each bound variable.
   */
  std::vector<TNode> d_canonVars;
  /** The match terms + their requirements */
  std::map<TNode, std::vector<Node>> d_matcherEqReq;
  std::map<TNode, std::vector<Node>> d_matcherDeqReq;
  /** List of all match terms */
  std::vector<TNode> d_matchers;
  //------------------- within search
  /** is alive, false if we know it is not possible to construct a propagating
   * instance for this quantified formula  */
  context::CDO<bool> d_isActive;
  /** index in matchers */
  context::CDO<size_t> d_watchMatcherIndex;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
