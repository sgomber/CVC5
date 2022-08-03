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
 * The solver for SMT queries in an SolverEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__SMT_SOLVER_DRIVER_H
#define CVC5__SMT__SMT_SOLVER_DRIVER_H

#include <vector>

#include "expr/node.h"
#include "smt/assertions.h"
#include "smt/env_obj.h"
#include "util/result.h"

namespace cvc5::internal {
namespace smt {

class SmtSolver;

enum class CheckAgainStatus
{
  PREPROCESS_SOLVE_AGAIN,
  SOLVE_AGAIN,
  FINISH
};

class SmtSolverDriver : protected EnvObj
{
 public:
  SmtSolverDriver(Env& env, SmtSolver& smt);
  virtual void notifyInputFormulas(
      std::vector<Node> ppAssertions,
      std::unordered_map<size_t, Node> ppSkolemMap) = 0;
  virtual void finishCheckSat(Result r) = 0;
  /**
   * Return true if we should check again. If so, we populate assertions
   * with the set of things that should be preprocessed
   */
  virtual CheckAgainStatus checkAgain(Assertions& as) = 0;

 protected:
  /** The underlying SMT solver */
  SmtSolver& d_smt;
};

class SmtSolverDriverSingleCall : public SmtSolverDriver
{
 public:
  SmtSolverDriverSingleCall(Env& env, SmtSolver& smt);
  void notifyInputFormulas(
      std::vector<Node> ppAssertions,
      std::unordered_map<size_t, Node> ppSkolemMap) override;
  void finishCheckSat(Result r) override;
  CheckAgainStatus checkAgain(Assertions& as) override;
};

class SmtSolverDriverDeepRestarts : public SmtSolverDriver
{
 public:
  SmtSolverDriverDeepRestarts(Env& env, SmtSolver& smt);
  void notifyInputFormulas(
      std::vector<Node> ppAssertions,
      std::unordered_map<size_t, Node> ppSkolemMap) override;
  void finishCheckSat(Result r) override;
  CheckAgainStatus checkAgain(Assertions& as) override;

 private:
  /** The current learned literals */
  std::vector<Node> d_zll;
  /** All learned literals, used for debugging */
  std::unordered_set<Node> d_allLearnedLits;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
