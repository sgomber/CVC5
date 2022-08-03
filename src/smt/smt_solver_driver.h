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
  SmtSolverDriver(Env& env, SmtSolver* smt) : EnvObj(env), d_smt(smt) {}
  virtual void notifyInputFormulas(
      std::vector<Node> ppAssertions,
      std::unordered_map<size_t, Node> ppSkolemMap) = 0;
  virtual void finishCheckSat(Result r) = 0;
  enum class CheckAgainStatus
  {
    PREPROCESS_SOLVE_AGAIN,
    SOLVE_AGAIN,
    FINISH
  };
  /**
   * Return true if we should check again. If so, we populate assertions
   * with the set of things that should be preprocessed
   */
  virtual CheckAgainStatus checkAgain(Assertions& as) = 0;

 private:
  /** The underlying SMT solver */
  SmtSolver* d_smt;
};

class SmtSolverDriverSingleCall : public SmtSolverDriver
{
 public:
  SmtSolverDriverSingleCall(Env& env, SmtSolver* smt) : SmtSolverDriver(env, smt) {}

  void notifyInputFormulas(
      std::vector<Node> ppAssertions,
      std::unordered_map<size_t, Node> ppSkolemMap) override
  {
    // immediately assert all formulas to the underlying prop engine
    d_smt->getPropEngine()->assertInputFormulas(ppAssertions, ppSkolemMap);
  }
  void finishCheckSat(Result r) override
  {
    // do nothing
  }
  CheckAgainStatus checkAgain(Assertions& as) override
  {
    return CheckAgainStatus::FINISH;
  }
};

class SmtSolverDriverDeepRestarts : public SmtSolverDriver
{
 public:
  SmtSolverDriverDeepRestarts(Env& env, SmtSolver* smt) : SmtSolverDriver(env, smt) {}

  void notifyInputFormulas(
      std::vector<Node> ppAssertions,
      std::unordered_map<size_t, Node> ppSkolemMap) override
  {
    // immediately assert all formulas to the underlying prop engine
    d_smt->getPropEngine()->assertInputFormulas(ppAssertions, ppSkolemMap);
  }
  
  void finishCheckSat(Result r) override
  {
    d_zll.clear();
    d_zll = d_smt->getPropEngine()->getLearnedZeroLevelLiteralsForRestart();
  }
  CheckAgainStatus checkAgain(Assertions& as) override
  {
    if (d_zll.empty())
    {
      return CheckAgainStatus::FINISH;
    }
    Trace("deep-restart") << "Have " << d_zll.size()
                          << " zero level learned literals" << std::endl;

    preprocessing::AssertionPipeline& apr = as.getAssertionPipeline();
    // Copy the preprocessed assertions and skolem map information directly
    for (const Node& a : d_ppAssertions)
    {
      apr.push_back(a);
    }
    preprocessing::IteSkolemMap& ismr = apr.getIteSkolemMap();
    for (const std::pair<const size_t, Node>& k : d_ppSkolemMap)
    {
      // carry the entire skolem map, which should align with the order of
      // assertions passed into the new assertions pipeline
      ismr[k.first] = k.second;
    }
    if (isOutputOn(OutputTag::DEEP_RESTART))
    {
      output(OutputTag::DEEP_RESTART) << "(deep-restart (";
      bool firstTime = true;
      for (TNode lit : zll)
      {
        output(OutputTag::DEEP_RESTART) << (firstTime ? "" : " ") << lit;
        firstTime = false;
      }
      output(OutputTag::DEEP_RESTART) << "))" << std::endl;
    }
    for (TNode lit : zll)
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
private:
  /** The current learned literals */
  std::vector<Node> d_zll;
  /** All learned literals, used for debugging */
  std::unordered_set<Node> d_allLearnedLits;
};

}
}

#endif
