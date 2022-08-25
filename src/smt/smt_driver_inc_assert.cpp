/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
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

#include "smt/smt_driver_inc_assert.h"

#include "options/base_options.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "smt/smt_solver.h"

namespace cvc5::internal {
namespace smt {

SmtDriverIncAssert::SmtDriverIncAssert(Env& env,
                                       SmtSolver& smt,
                                       ContextManager* ctx)
    : SmtDriver(env, smt, ctx), d_initialized(false)
{
}

Result SmtDriverIncAssert::checkSatNext(bool& checkAgain)
{
  Assertions& as = d_smt.getAssertions();
  d_smt.preprocess(as);
  if (!d_initialized)
  {
    d_ppAsserts = d_smt.getPreprocessedAssertions();
    d_ppSkolemMap = d_smt.getPreprocessedSkolemMap();
    checkAgain = true;
    d_initialized = true;
    return Result();
  }
  d_smt.assertToInternal(as);
  Result result = d_smt.checkSatInternal();
  return result;
}

void SmtDriverIncAssert::getNextAssertions(Assertions& as) {}

}  // namespace smt
}  // namespace cvc5::internal
