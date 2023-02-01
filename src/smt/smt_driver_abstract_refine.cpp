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

#include "smt/smt_driver_abstract_refine.h"

#include "prop/prop_engine.h"
#include "smt/env.h"
#include "smt/smt_solver.h"

namespace cvc5::internal {
namespace smt {

SmtDriverAbstractRefine::SmtDriverAbstractRefine(Env& env, SmtSolver& smt, ContextManager* ctx) :
SmtDriver(env, smt, ctx), d_initialized(false)
{
   
}

Result SmtDriverAbstractRefine::checkSatNext(preprocessing::AssertionPipeline& ap)
{
  d_smt.preprocess(ap);
  d_smt.assertToInternal(ap);
  Result result = d_smt.checkSatInternal();
  // check again if we didn't solve and there are learned literals
  if (result.getStatus() == Result::SAT)
  {
    if (!checkModel())
    {
      return Result(Result::UNKNOWN, REQUIRES_CHECK_AGAIN);
    }
  }
  return result;
}

void SmtDriverAbstractRefine::getNextAssertions(preprocessing::AssertionPipeline& ap)
{
  if (!d_initialized)
  {
    // On the first time, we take the Boolean abstraction of all assertions.
    Assertions& as = d_smt.getAssertions();
    const context::CDList<Node>& al = as.getAssertionList();
    for (const Node& a : al)
    {
      d_currAssertions.push_back(booleanAbstractionOf(a));
    }
    d_initialized = true;
  }
  // take all assertions
   for (const Node& a : d_currAssertions)
   {
      ap.push_back(a, true);
   }
}

Node SmtDriverAbstractRefine::booleanAbstractionOf(const Node& n)
{
   return n;
}

bool SmtDriverAbstractRefine::checkModel()
{
   return true;
}

}  // namespace smt
}  // namespace cvc5::internal
