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

#include <map>
#include <vector>

#include "theory/strings/base_solver.h"
#include "theory/strings/infer_info.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/normal_form.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/term_registry.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 */
class StringsMnf : protected EnvObj
{
 public:
  StringsMnf(Env& env,
             SolverState& s,
             InferenceManager& im,
             TermRegistry& tr,
             BaseSolver& bs);
  ~StringsMnf();
  
  /** find model normal forms */
  bool findModelNormalForms(const std::vector<Node>& stringsEqc);
protected:
  /** The solver state object */
  SolverState& d_state;
  /** The (custom) output channel of the theory of strings */
  InferenceManager& d_im;
  /** Reference to the term registry of theory of strings */
  TermRegistry& d_termReg;
  /** reference to the base solver, used for certain queries */
  BaseSolver& d_bsolver;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__STRINGS_MNF_H */
