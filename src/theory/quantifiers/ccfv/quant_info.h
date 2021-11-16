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
#include "theory/uf/equality_engine.h"

namespace cvc5 {

namespace expr {
class TermCanonize;
}

namespace theory {
namespace quantifiers {
namespace ccfv {

class QuantInfo
{
  using NodeBoolPairHashFunction =
      PairHashFunction<Node, bool, std::hash<Node>>;

 public:
  QuantInfo(context::Context* c);
  /**
   * Initialize, called once.
   */
  void initialize(TNode q, eq::EqualityEngine* ee, expr::TermCanonize& tc);
  //-------------------------- static information
  /** Get free variables */
  const std::vector<TNode>& getFreeVariables() const;
  /**
   * Get ordered free variables
   */
  const std::vector<TNode>& getOrderedFreeVariables() const;
  /**
   * Get the constraints, which maps pattern terms to node corresponding to
   * their constraints for making the quantified formula have a propagating
   * instance. For details on the range of constraints, see d_req.
   */
  const std::map<TNode, std::vector<Node>>& getConstraints() const;
  /** Get the constraint terms */
  const std::vector<TNode>& getConstraintTerms() const;
  /** Get congruence terms, the terms to add to the equality engine */
  const std::vector<TNode>& getCongruenceTerms() const;
  /** Get congruence term variable map */
  const std::map<TNode, TNode>& getTermMaxVarMap() const;
  //-------------------------- per round
  /** reset variable count */
  // void resetSearchVariableCount();
  /**
   * Get next variable. This is used to initialize the search.
   */
  TNode getNextSearchVariable();
  //-------------------------- per round
  /**
   * Reset round, called once per full effort check
   */
  void resetRound();
  /** get the matcher for variable v */
  TNode getMatcherFor(TNode v) const;
  /** Is alive? */
  bool isActive() const;
  /** set dead */
  void setActive(bool val);

  /** is c a disequality constraint for p? */
  static bool isDeqConstraint(TNode c, TNode p, TNode& val);
  /** is c a disequality constraint for p? */
  static bool isDeqConstraint(TNode c, TNode p);

  /** Debug print */
  std::string toStringDebug() const;

 private:
  /**
   * Process matching requirement for subterm cur which is a disjunct in the
   * quantified formula of this class.
   */
  void computeMatchReq(TNode cur,
                       eq::EqualityEngine* ee,
                       std::vector<TNode>& visit);
  /** Add match term that must be (dis)equal from eqc */
  void addMatchTermReq(TNode t, Node eqc, bool isEq);
  /** Process match requirement terms */
  void processMatchReqTerms(eq::EqualityEngine* ee);
  //------------------- static
  /** The quantified formula */
  Node d_quant;
  /** Canonical form of body */
  Node d_canonBody;
  /**
   * List of canonical variables corresponding to each bound variable.
   */
  std::vector<TNode> d_canonVars;
  /**
   * Ordered list of canon variables, ensures that the index of the variables
   * from term canonization is minimal lexiocographically.
   */
  std::vector<TNode> d_canonVarOrdered;
  /**
   * The match terms maped to their requirements. A requirement for p can be:
   * (1) Node::null(), saying that the term must be equal to any ground term
   * (2) (not (= p g)), saying that pattern must be disequal from g
   * (3) g, saying that the pattern must be equal to g
   */
  std::map<TNode, std::vector<Node>> d_req;
  /** The domain of d_req */
  std::vector<TNode> d_reqTerms;
  /**
   * List of all "congruence terms". This is the set of all subterms of the
   * domain of d_req whose kind we are doing congruence over in the equality
   * engine that this class was initialized for.
   */
  std::vector<TNode> d_congTerms;
  /**
   * The maximum variable for each term. For each pattern subterm
   * t, this is the variable that occurs in t that has a maximum index in
   * d_canonVarOrdered.
   *
   * This variable is used for tracking the variable which, when assigned,
   * makes the congruence term fully assigned.
   */
  std::map<TNode, TNode> d_termMaxVar;
  /**
   * Mapping from free variables to a "matcher" for that variable. These terms
   * determine what to invoke matching on.
   *
   * A matcher for variable v:
   * (1) is a top-level congruence term, i.e. one that occurs as a subterm in
   * the domain of d_req in positions that are not nested under other congruence
   * terms.
   * (2) is such that no other matcher t for v' exists that contains v, where
   * v' < v. In other words, matchers for earlier variables in the variable
   * order do not bind v.
   */
  std::map<TNode, TNode> d_matchers;
  /**
   * Subterms of d_req that we don't handle.
   */
  std::unordered_set<TNode> d_unknownTerms;
  //------------------- initializing search
  /** init variable index */
  size_t d_initVarIndex;
  //------------------- within search
  /** is alive, false if we know it is not possible to construct a propagating
   * instance for this quantified formula  */
  context::CDO<bool> d_isActive;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
