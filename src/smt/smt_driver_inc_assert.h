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

#ifndef CVC5__SMT__SMT_DRIVER_INC_ASSERT_H
#define CVC5__SMT__SMT_DRIVER_INC_ASSERT_H

#include "smt/smt_driver.h"
#include "util/result.h"

namespace cvc5::internal {
namespace smt {

class SmtSolver;
class ContextManager;

class SmtDriverIncAssert : public SmtDriver
{
 public:
  SmtDriverIncAssert(Env& env, SmtSolver& smt, ContextManager* ctx);

 protected:
  Result checkSatNext(bool& checkAgain) override;
  void getNextAssertions(Assertions& as) override;

 private:
  /** Initialized */
  bool d_initialized;
  /** The original preprocessed assertions */
  std::vector<Node> d_ppAsserts;
  /** The original skolem map */
  std::unordered_map<size_t, Node> d_ppSkolemMap;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
