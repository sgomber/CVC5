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
  Result result;
  try
  {
    // then, initialize the assertions
    as.setAssumptions(assumptions);

    // make the check, where notice smt engine should be fully inited by now

    Trace("smt") << "SmtSolver::check()" << std::endl;

    ResourceManager* rm = d_env.getResourceManager();
    if (rm->out())
    {
      UnknownExplanation why = rm->outOfResources()
                                   ? UnknownExplanation::RESOURCEOUT
                                   : UnknownExplanation::TIMEOUT;
      result = Result(Result::UNKNOWN, why);
    }
    else
    {
      rm->beginCall();

      bool checkAgain = true;
      while (checkAgain)
      {
        checkAgain = false;
        result = checkSatNext(as, checkAgain);
        if (checkAgain)
        {
          as.clearCurrent();
          // get the next assertions
          getNextAssertions(as);
          // finish init to construct new theory/prop engine
          d_smt.finishInit();
        }
      }

      rm->endCall();
      Trace("limit") << "SmtSolver::check(): cumulative millis "
                     << rm->getTimeUsage() << ", resources "
                     << rm->getResourceUsage() << std::endl;
    }
  }
  catch (const LogicException& e)
  {
    // The exception may have been throw during solving, backtrack to reset the
    // decision level to the level expected after this method finishes
    d_smt.getPropEngine()->resetTrail();
    throw;
  }

  return result;
}

SmtSolverDriverSingleCall::SmtSolverDriverSingleCall(Env& env, SmtSolver& smt)
    : SmtSolverDriver(env, smt)
{
}

Result SmtSolverDriverSingleCall::checkSatNext(Assertions& as, bool& checkAgain)
{
  d_smt.preprocess(as);
  d_smt.assertToInternal(as);
  Result result = d_smt.checkSatInternal();
  return result;
}

void SmtSolverDriverSingleCall::getNextAssertions(Assertions& as)
{
  Assert(false);
}

SmtSolverDriverDeepRestarts::SmtSolverDriverDeepRestarts(Env& env,
                                                         SmtSolver& smt)
    : SmtSolverDriver(env, smt)
{
}

Result SmtSolverDriverDeepRestarts::checkSatNext(Assertions& as,
                                                 bool& checkAgain)
{
  d_smt.preprocess(as);
  d_smt.assertToInternal(as);
  Result result = d_smt.checkSatInternal();
  // get the learned literals immediately
  d_zll.clear();
  d_zll = d_smt.getPropEngine()->getLearnedZeroLevelLiteralsForRestart();
  // check again if we didn't solve and there are learned literals
  if (!d_zll.empty() && result.getStatus() == Result::UNKNOWN)
  {
    checkAgain = true;
  }
  return result;
}

void SmtSolverDriverDeepRestarts::getNextAssertions(Assertions& as)
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
