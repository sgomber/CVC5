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

#ifndef CVC5__SMT__SMT_DRIVER_H
#define CVC5__SMT__SMT_DRIVER_H

#include <vector>

#include "expr/node.h"
#include "smt/assertions.h"
#include "smt/env_obj.h"
#include "util/result.h"

namespace cvc5::internal {
namespace smt {

class SmtSolver;
class ContextManager;

class SmtDriver : protected EnvObj
{
 public:
  SmtDriver(Env& env, SmtSolver& smt, ContextManager& ctx);

  /**
   * Check satisfiability (used to check satisfiability and entailment)
   * in SolverEngine. This is done via adding assumptions (when necessary) to
   * assertions as, preprocessing and pushing assertions into the prop engine
   * of this class, and checking for satisfiability via the prop engine.
   *
   * @param assumptions The assumptions for this check-sat call, which are
   * temporary assertions.
   */
  Result checkSatisfiability(const std::vector<Node>& assumptions);

 protected:
  virtual Result checkSatNext(bool& checkAgain) = 0;
  /**
   * Get the next assertions. This is called immediately after checkSatNext
   * where checkAgain has been set to true. This populates assertions with
   * those that will be checked on the next call to checkSatNext.
   *
   * Note that as is always the assertions of the underlying solver d_smt
   * currently.
   */
  virtual void getNextAssertions(Assertions& as) = 0;
  /** The underlying SMT solver */
  SmtSolver& d_smt;
  /** The underlying context manager */
  ContextManager& d_ctx;
};

class SmtDriverSingleCall : public SmtDriver
{
 public:
  SmtDriverSingleCall(Env& env, SmtSolver& smt, ContextManager& ctx);

 protected:
  Result checkSatNext(bool& checkAgain) override;
  void getNextAssertions(Assertions& as) override;
};

class SmtDriverDeepRestarts : public SmtDriver
{
 public:
  SmtDriverDeepRestarts(Env& env, SmtSolver& smt, ContextManager& ctx);

 protected:
  Result checkSatNext(bool& checkAgain) override;
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
