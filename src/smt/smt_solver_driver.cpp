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
#include "smt/smt_solver.h"

namespace cvc5::internal {
namespace smt {

SmtSolverDriver::SmtSolverDriver(Env& env, SmtSolver& smt)
    : EnvObj(env), d_smt(smt)
{
}

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
CheckAgainStatus SmtSolverDriverSingleCall::checkAgain(Assertions& as)
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
CheckAgainStatus SmtSolverDriverDeepRestarts::checkAgain(Assertions& as)
{
  if (d_zll.empty())
  {
    return CheckAgainStatus::FINISH;
  }
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

  return CheckAgainStatus::FINISH;
}

}  // namespace smt
}  // namespace cvc5::internal
