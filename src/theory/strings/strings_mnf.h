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
 * Model normal form finder for strings
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__STRINGS_MNF_H
#define CVC5__THEORY__STRINGS__STRINGS_MNF_H

#include "theory/strings/infer_info.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/model_cons.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/term_registry.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

class BaseSolver;
class CoreSolver;

class ModelEqcInfo
{
 public:
  ModelEqcInfo() {}
  ~ModelEqcInfo() {}
  /**
   * The current normal form.
   * Normal form is a list of pairs (t,l) where t is an atomic representative
   * and l is the model value for its length.
   */
  std::vector<Node> d_mnf;
  /** The length value */
  Rational d_length;
  /** To string (for debugging) */
  std::string toString() const;
  /** Expand all occurrences of n in mnf with the list nn. */
  static void expandNormalForm(std::vector<Node>& mnf,
                               const Node& n,
                               const std::vector<Node>& nn);
  /** Call the above method for d_mnf. */
  void expand(const Node& n, const std::vector<Node>& nn);
};

/**
 */
class StringsMnf : protected ModelCons
{
 public:
  StringsMnf(Env& env,
             SolverState& s,
             InferenceManager& im,
             TermRegistry& tr,
             BaseSolver& bs,
             CoreSolver& cs);
  ~StringsMnf() {}

  /** Check model normal forms */
  bool checkModelNormalforms();

  /**
   * Has candidate model, which returns true, since this class is
   * assigned as the model constructor only when it is certain there is a model.
   */
  bool hasCandidateModel() override;
  /** Get string representatives from */
  void getStringRepresentativesFrom(
      const std::set<Node>& termSet,
      std::unordered_set<TypeNode>& repTypes,
      std::map<TypeNode, std::unordered_set<Node>>& repSet,
      std::vector<Node>& auxEq) override;
  /** Separate by length */
  void separateByLength(const std::vector<Node>& ns,
                        std::vector<std::vector<Node>>& cols,
                        std::vector<Node>& lts) override;
  /** Get normal form */
  std::vector<Node> getNormalForm(Node n) override;

 protected:
  /**
   * Normalize eqc.
   *
   * Ensures that a normal form can be set for all concatenation and constant
   * terms in eqc.
   *
   * If returns true, ModelEqcInfo is set for eqc.
   */
  bool normalizeEqc(Node eqc);
  /**
   * Normalize deq.
   */
  bool normalizeDeq(Node a, Node b);
  /** Get normal form internal, assumes r is a model representative */
  std::vector<Node> getNormalFormInternal(const Node& r);
  /** Get length */
  Rational getLength(const Node& r);
  /** Get model representative */
  Node getModelRepresentative(const Node& n);
  /** Merge */
  void merge(const Node& a, const Node& b);
  /** Split */
  std::vector<Node> split(const Node& a,
                          const Rational& alen,
                          const Rational& pos);
  /** Expand n -> nn in all normal forms */
  void expandNormalForms(const Node& n, const std::vector<Node>& nn);
  /** The solver state object */
  SolverState& d_state;
  /** The (custom) output channel of the theory of strings */
  InferenceManager& d_im;
  /** Reference to the term registry of theory of strings */
  TermRegistry& d_termReg;
  /** reference to the base solver, used for certain queries */
  BaseSolver& d_bsolver;
  /** reference to the core solver, used for certain queries */
  CoreSolver& d_csolver;
  /** Common constants */
  Node d_zero;
  /** Maximum model length */
  uint64_t d_maxModelLen;
  /** Map from representatives to information */
  std::map<Node, ModelEqcInfo> d_minfo;
  /**
   * Map from representatives in equality engine or allocated model
   * representatives to their model representative.
   */
  std::map<Node, Node> d_mrepMap;
  /**
   * Constant-like
   */
  std::vector<std::pair<Node, Node>> d_constLike;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__STRINGS_MNF_H */
