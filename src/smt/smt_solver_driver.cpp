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

#include "smt/smt_solver_driver.h"

#include "options/base_options.h"
#include "options/main_options.h"
#include "options/smt_options.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "smt/smt_solver.h"

namespace cvc5::internal {
namespace smt {

SmtSolverDriver::SmtSolverDriver(Env& env, SmtSolver& smt)
    : EnvObj(env), d_smt(smt)
{
}

Result SmtSolverDriver::checkSatisfiability(
    Assertions& as, const std::vector<Node>& assumptions)
{
  Result r = runCheckSatWithPreprocess(as, assumptions);
  bool runCheckAgain = true;
  while (runCheckAgain)
  {
    CheckAgainStatus cas = checkAgain();
    bool runCheckWithPreprocess = true;
    if (cas == CheckAgainStatus::FINISH)
    {
      runCheckAgain = false;
    }
    else if (cas == CheckAgainStatus::PREPROCESS_SOLVE_AGAIN)
    {
      as.clearCurrent();
      // finish init the SMT solver, which reconstructs the theory engine and
      // prop engine.
      populateAssertions(as);
      d_smt.finishInit();
    }
    else if (cas == CheckAgainStatus::SOLVE_AGAIN)
    {
      runCheckWithPreprocess = false;
    }
  }
  return r;
}

Result SmtSolverDriver::runCheckSatWithPreprocess(
    Assertions& as, const std::vector<Node>& assumptions)
{
  Result result;
  /*
  try
  {
    // then, initialize the assertions
    as.initializeCheckSat(assumptions);

    // make the check, where notice smt engine should be fully inited by now

    Trace("smt") << "SmtSolver::check()" << std::endl;

    // Make sure the prop layer has all of the assertions
    Trace("smt") << "SmtSolver::check(): processing assertions" << std::endl;
    d_smt.processAssertions(as);
    Trace("smt") << "SmtSolver::check(): done processing assertions"
                 << std::endl;

    d_env.verbose(2) << "solving..." << std::endl;
    Trace("smt") << "SmtSolver::check(): running check" << std::endl;
    result = d_smt.checkSatisfiability();
    Trace("smt") << "SmtSolver::check(): result " << result << std::endl;
  }
  catch (const LogicException& e)
  {
    // The exception may have been throw during solving, backtrack to reset the
    // decision level to the level expected after this method finishes
    d_smt.getPropEngine()->resetTrail();
    throw;
  }
*/
  // set the filename on the result
  const std::string& filename = options().driver.filename;
  return Result(result, filename);
}

Result SmtSolverDriver::runCheckSat() {}

SmtSolverDriverSingleCall::SmtSolverDriverSingleCall(Env& env, SmtSolver& smt)
    : SmtSolverDriver(env, smt)
{
}

void SmtSolverDriverSingleCall::notifyInputFormulas(
    std::vector<Node> ppAssertions,
    std::unordered_map<size_t, Node> ppSkolemMap)
{
  // immediately assert all formulas to the underlying prop engine
  d_smt.getPropEngine()->assertInputFormulas(ppAssertions, ppSkolemMap);
}
void SmtSolverDriverSingleCall::finishCheckSat(Result r)
{
  // do nothing
}
CheckAgainStatus SmtSolverDriverSingleCall::checkAgain()
{
  return CheckAgainStatus::FINISH;
}

SmtSolverDriverDeepRestarts::SmtSolverDriverDeepRestarts(Env& env,
                                                         SmtSolver& smt)
    : SmtSolverDriver(env, smt)
{
}

void SmtSolverDriverDeepRestarts::notifyInputFormulas(
    std::vector<Node> ppAssertions,
    std::unordered_map<size_t, Node> ppSkolemMap)
{
  // immediately assert all formulas to the underlying prop engine
  d_smt.getPropEngine()->assertInputFormulas(ppAssertions, ppSkolemMap);
}

void SmtSolverDriverDeepRestarts::finishCheckSat(Result r)
{
  d_zll.clear();
  d_zll = d_smt.getPropEngine()->getLearnedZeroLevelLiteralsForRestart();
}
CheckAgainStatus SmtSolverDriverDeepRestarts::checkAgain()
{
  if (d_zll.empty())
  {
    return CheckAgainStatus::FINISH;
  }
  return CheckAgainStatus::PREPROCESS_SOLVE_AGAIN;
}

void SmtSolverDriverDeepRestarts::populateAssertions(Assertions& as)
{
  Trace("deep-restart") << "Have " << d_zll.size()
                        << " zero level learned literals" << std::endl;
  preprocessing::AssertionPipeline& apr = as.getAssertionPipeline();
  // Copy the preprocessed assertions and skolem map information directly
  const std::vector<Node>& ppAssertions = d_smt.getPreprocessedAssertions();
  for (const Node& a : ppAssertions)
  {
    apr.push_back(a);
  }
  preprocessing::IteSkolemMap& ismr = apr.getIteSkolemMap();
  const std::unordered_map<size_t, Node>& ppSkolemMap =
      d_smt.getPreprocessedSkolemMap();
  for (const std::pair<const size_t, Node>& k : ppSkolemMap)
  {
    // carry the entire skolem map, which should align with the order of
    // assertions passed into the new assertions pipeline
    ismr[k.first] = k.second;
  }
  if (isOutputOn(OutputTag::DEEP_RESTART))
  {
    output(OutputTag::DEEP_RESTART) << "(deep-restart (";
    bool firstTime = true;
    for (TNode lit : d_zll)
    {
      output(OutputTag::DEEP_RESTART) << (firstTime ? "" : " ") << lit;
      firstTime = false;
    }
    output(OutputTag::DEEP_RESTART) << "))" << std::endl;
  }
  for (TNode lit : d_zll)
  {
    Trace("deep-restart-lit") << "Restart learned lit: " << lit << std::endl;
    apr.push_back(lit);
    if (Configuration::isAssertionBuild())
    {
      Assert(d_allLearnedLits.find(lit) == d_allLearnedLits.end())
          << "Relearned: " << lit << std::endl;
      d_allLearnedLits.insert(lit);
    }
  }
  Trace("deep-restart") << "Finished compute deep restart" << std::endl;
}

}  // namespace smt
}  // namespace cvc5::internal
