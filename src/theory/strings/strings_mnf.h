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

#include "theory/strings/base_solver.h"
#include "theory/strings/infer_info.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/model_cons.h"
#include "theory/strings/normal_form.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/term_registry.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

class ModelEqcInfo
{
public:
    ModelEqcInfo(){}
    ~ModelEqcInfo(){}
    /** The current normal form */
    std::vector<Node> d_mnf;
    /** The length value */
    Node d_length;
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
             BaseSolver& bs);
  ~StringsMnf() {}

  /** find model normal forms */
  bool findModelNormalForms(const std::vector<Node>& stringsEqc);

  /** Get string representatives from */
  void getStringRepresentativesFrom(
      const std::set<Node>& termSet,
      std::unordered_set<TypeNode>& repTypes,
      std::map<TypeNode, std::unordered_set<Node>>& repSet) override;
  /** Separate by length */
  void separateByLength(
      const std::vector<Node>& n,
      std::map<TypeNode, std::vector<std::vector<Node>>>& cols,
      std::map<TypeNode, std::vector<Node>>& lts) override;
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
  bool normalizeEqc(Node eqc, TypeNode stype);
  /** 
   * Expand normal form, which returns a vector from nf where all terms in the
   * returned vector are atomic.
   */
  std::vector<Node> expandNormalForm(const std::vector<Node>& nf);
  /** The solver state object */
  SolverState& d_state;
  /** The (custom) output channel of the theory of strings */
  InferenceManager& d_im;
  /** Reference to the term registry of theory of strings */
  TermRegistry& d_termReg;
  /** reference to the base solver, used for certain queries */
  BaseSolver& d_bsolver;
  /** Common constants */
  Node d_zero;
  /** Map from representatives to information */
  std::map<Node, ModelEqcInfo > d_minfo;
  /** Map from atomic variables to representative */
  std::map<Node, Node> d_repMap;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__STRINGS_MNF_H */
