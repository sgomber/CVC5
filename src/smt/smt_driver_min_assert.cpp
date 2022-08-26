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

#include "smt/smt_driver_min_assert.h"

#include "options/base_options.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "smt/smt_solver.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace smt {

SmtDriverMinAssert::SmtDriverMinAssert(Env& env,
                                       SmtSolver& smt,
                                       ContextManager* ctx)
    : SmtDriver(env, smt, ctx), d_initialized(false), d_nextIndexToInclude(0)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

Result SmtDriverMinAssert::checkSatNext(bool& checkAgain)
{
  Trace("smt-min-assert") << "--- checkSatNext #models=" << d_modelValues.size()
                          << std::endl;
  Trace("smt-min-assert") << "checkSatNext: preprocess" << std::endl;
  Assertions& as = d_smt.getAssertions();
  d_smt.preprocess(as);
  if (!d_initialized)
  {
    // just preprocess on the first check, preprocessed assertions will be
    // recorded below
    checkAgain = true;
    Trace("smt-min-assert") << "...return, initialize" << std::endl;
    return Result();
  }
  Trace("smt-min-assert") << "checkSatNext: assertToInternal" << std::endl;
  d_smt.assertToInternal(as);
  Trace("smt-min-assert") << "checkSatNext: checkSatInternal" << std::endl;
  Result result = d_smt.checkSatInternal();
  // if UNSAT, we are done
  if (result.getStatus() == Result::UNSAT)
  {
    Trace("smt-min-assert") << "...return, UNSAT" << std::endl;
    return result;
  }
  Trace("smt-min-assert") << "checkSatNext: recordCurrentModel" << std::endl;
  bool allAssertsSat;
  if (recordCurrentModel(allAssertsSat))
  {
    checkAgain = true;
    Trace("smt-min-assert") << "...return, check again" << std::endl;
  }
  else if (allAssertsSat)
  {
    Trace("smt-min-assert") << "...return, SAT" << std::endl;
    // a model happened to satisfy every assertion
    return Result(Result::SAT);
  }
  else
  {
    Trace("smt-min-assert") << "...return, (fail) " << result << std::endl;
  }
  // Otherwise, we take the current result (likely unknown).
  // If result happens to be SAT, then we are in a case where the model doesnt
  // satisfy an assertion that was included, in which case we trust the
  // checkSatInternal result.
  return result;
}

void SmtDriverMinAssert::getNextAssertions(Assertions& as)
{
  if (!d_initialized)
  {
    // TODO: split AND
    d_ppAsserts = d_smt.getPreprocessedAssertions();
    d_ppSkolemMap = d_smt.getPreprocessedSkolemMap();
    Trace("smt-min-assert") << "Have " << d_ppAsserts.size()
                            << " preprocessed assertions" << std::endl;
    d_initialized = true;
    // do not provide any assertions initially
    return;
  }
  // should have set d_nextIndexToInclude which is not already included
  Assert(d_nextIndexToInclude < d_ppAsserts.size());
  Assert(d_ainfo.find(d_nextIndexToInclude) == d_ainfo.end());
  // initialize the assertion info
  AssertInfo& ainext = d_ainfo[d_nextIndexToInclude];
  // check if it has a corresponding skolem
  std::unordered_map<size_t, Node>::iterator itk =
      d_ppSkolemMap.find(d_nextIndexToInclude);
  if (itk != d_ppSkolemMap.end())
  {
    ainext.d_skolem = itk->second;
  }
  Assert(!d_modelValues.empty());
  // we assume it takes the current model
  size_t currModelIndex = d_modelValues.size() - 1;
  d_modelToAssert[currModelIndex] = d_nextIndexToInclude;
  ainext.d_coverModels++;
  Trace("smt-min-assert") << "Add assertion #" << d_nextIndexToInclude << ": "
                          << d_ppAsserts[d_nextIndexToInclude] << std::endl;

  // iterate over previous models
  std::unordered_map<size_t, size_t>::iterator itp;
  std::map<size_t, AssertInfo>::iterator ita;
  for (size_t i = 0; i < currModelIndex; i++)
  {
    Assert(d_modelValues[i].size() == d_ppAsserts.size());
    Node vic = d_modelValues[i][d_nextIndexToInclude];
    // determine if this assertion should take ownership of the i^th model
    bool coverModel = false;
    if (vic == d_false)
    {
      // we take all models we were false on
      coverModel = true;
    }
    else if (vic.isNull() && d_unkModels.find(i) != d_unkModels.end())
    {
      // we take models we were unknown on that did not have a false assertion
      coverModel = true;
    }
    if (coverModel)
    {
      // decrement the count of the assertion
      itp = d_modelToAssert.find(i);
      Assert(itp != d_modelToAssert.end());
      Assert(itp->second != d_nextIndexToInclude);
      ita = d_ainfo.find(itp->second);
      Assert(ita != d_ainfo.end());
      ita->second.d_coverModels--;
      if (ita->second.d_coverModels == 0)
      {
        Trace("smt-min-assert")
            << "Remove assertion #" << itp->second << std::endl;
        // a previous assertion no longer is necessary
        d_ainfo.erase(ita);
      }
      d_modelToAssert[i] = d_nextIndexToInclude;
      ainext.d_coverModels++;
    }
  }
  Trace("smt-min-assert") << "...covers " << ainext.d_coverModels << " models"
                          << std::endl;

  // now have a list of assertions to include
  preprocessing::AssertionPipeline& apr = as.getAssertionPipeline();
  preprocessing::IteSkolemMap& ismr = apr.getIteSkolemMap();
  for (std::pair<const size_t, AssertInfo>& a : d_ainfo)
  {
    Assert(a.first < d_ppAsserts.size());
    Assert(a.second.d_coverModels > 0);
    Node pa = d_ppAsserts[a.first];
    // carry the skolem mapping as well
    if (!a.second.d_skolem.isNull())
    {
      ismr[apr.size()] = a.second.d_skolem;
    }
    apr.push_back(pa);
  }
  Trace("smt-min-assert")
      << "...finished get next assertions, #current assertions = "
      << d_ainfo.size() << std::endl;
}

bool SmtDriverMinAssert::recordCurrentModel(bool& allAssertsSat)
{
  d_nextIndexToInclude = 0;
  allAssertsSat = true;
  bool indexSet = false;
  bool indexSetToFalse = false;
  TheoryEngine* te = d_smt.getTheoryEngine();
  Assert(te != nullptr);
  theory::TheoryModel* m = te->getBuiltModel();
  d_modelValues.emplace_back();
  std::vector<Node>& currModel = d_modelValues.back();
  for (size_t i = 0, nasserts = d_ppAsserts.size(); i < nasserts; i++)
  {
    Node a = d_ppAsserts[i];
    Node av = m->getValue(a);
    av = av.isConst() ? av : Node::null();
    currModel.push_back(av);
    if (av == d_true)
    {
      continue;
    }
    allAssertsSat = false;
    // if its already included in our assertions
    if (d_ainfo.find(i) != d_ainfo.end())
    {
      // we were unable to satisfy this assertion; the result from the last
      // check-sat was likely "unknown", we skip this assertion and look for
      // a different one
      continue;
    }
    if (indexSetToFalse)
    {
      // already have a false assertion
      continue;
    }
    bool isFalse = (av == d_false);
    if (!isFalse && indexSet)
    {
      // already have an unknown assertion
      continue;
    }
    // include this one, remembering if it is false or not
    d_nextIndexToInclude = i;
    indexSetToFalse = isFalse;
    indexSet = true;
  }
  // if we did not find a false assertion, remember it
  if (!allAssertsSat && !indexSetToFalse)
  {
    d_unkModels.insert(d_modelValues.size());
  }
  // we are successful if we have a new assertion to include
  return indexSet;
}

}  // namespace smt
}  // namespace cvc5::internal
