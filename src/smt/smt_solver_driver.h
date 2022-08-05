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

class SmtSolverDriver : protected EnvObj
{
 public:
  SmtSolverDriver(Env& env, SmtSolver& smt);

  /**
   * Check satisfiability (used to check satisfiability and entailment)
   * in SolverEngine. This is done via adding assumptions (when necessary) to
   * assertions as, preprocessing and pushing assertions into the prop engine
   * of this class, and checking for satisfiability via the prop engine.
   *
   * @param as The object managing the assertions in SolverEngine. This class
   * maintains a current set of (unprocessed) assertions which are pushed
   * into the internal members of this class (TheoryEngine and PropEngine)
   * during this call.
   * @param assumptions The assumptions for this check-sat call, which are
   * temporary assertions.
   */
  Result checkSatisfiability(Assertions& as,
                             const std::vector<Node>& assumptions);

 protected:
  virtual Result checkSatNext(Assertions& as, bool& checkAgain) = 0;
  virtual void getNextAssertions(Assertions& as) = 0;
  /** The underlying SMT solver */
  SmtSolver& d_smt;
};

class SmtSolverDriverSingleCall : public SmtSolverDriver
{
 public:
  SmtSolverDriverSingleCall(Env& env, SmtSolver& smt);

 protected:
  Result checkSatNext(Assertions& as, bool& checkAgain) override;
  void getNextAssertions(Assertions& as) override;
};

class SmtSolverDriverDeepRestarts : public SmtSolverDriver
{
 public:
  SmtSolverDriverDeepRestarts(Env& env, SmtSolver& smt);

 protected:
  Result checkSatNext(Assertions& as, bool& checkAgain) override;
  void getNextAssertions(Assertions& as) override;

 private:
  /** The current learned literals */
  std::vector<Node> d_zll;
  /** All learned literals, used for debugging */
  std::unordered_set<Node> d_allLearnedLits;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
