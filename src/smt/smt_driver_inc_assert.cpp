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
#include "theory/theory_engine.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace smt {

SmtDriverIncAssert::SmtDriverIncAssert(Env& env,
                                       SmtSolver& smt,
                                       ContextManager* ctx)
    : SmtDriver(env, smt, ctx), d_initialized(false), d_nextIndexToInclude(0)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

Result SmtDriverIncAssert::checkSatNext(bool& checkAgain)
{
  Assertions& as = d_smt.getAssertions();
  d_smt.preprocess(as);
  if (!d_initialized)
  {
    // just preprocess on the first check, preprocessed assertions will be
    // recorded below
    checkAgain = true;
    return Result();
  }
  d_smt.assertToInternal(as);
  Result result = d_smt.checkSatInternal();
  // if UNSAT, we are done
  if (result.getStatus() != Result::UNSAT)
  {
    if (recordCurrentModel())
    {
      // a model happened to satisfy every assertion
      result = Result(Result::SAT);
    }
    else
    {
      checkAgain = true;
    }
  }
  return result;
}

void SmtDriverIncAssert::getNextAssertions(Assertions& as) {
  if (!d_initialized)
  {
    d_ppAsserts = d_smt.getPreprocessedAssertions();
    std::unordered_map<size_t, Node> ppSkolemMap = d_smt.getPreprocessedSkolemMap();
    // convert to mapping between formulas and their definition
    for (std::pair<const size_t, Node>& pps : ppSkolemMap)
    {
      Assert (pps.first<d_ppAsserts.size());
      d_ppSkolemMap[d_ppAsserts[pps.first]] = pps.second;
    }
    d_initialized = true;
    // do not provide any assertions initially
    return;
  }
  // should have set d_nextIndexToInclude
  
  
  
  // now have a list of assertions to include
  preprocessing::AssertionPipeline& apr = as.getAssertionPipeline();
  preprocessing::IteSkolemMap& ismr = apr.getIteSkolemMap();
  for (std::pair<const size_t, AssertInfo>& a : d_ainfo)
  {
    Assert (a.first<d_ppAsserts.size());
    Assert (!a.second.d_cover.empty());
    Node pa = d_ppAsserts[a.first];
    apr.push_back(pa);
    // carry the skolem mapping as well
    if (!a.second.d_skolem.isNull())
    {
      
    }
  }
}

bool SmtDriverIncAssert::recordCurrentModel()
{
  bool indexSet = false;
  bool indexSetToFalse = false;
  TheoryEngine* te = d_smt.getTheoryEngine();
  Assert(te != nullptr);
  theory::TheoryModel* m = te->getBuiltModel();
  d_modelValues.emplace_back();
  std::vector<Node>& currModel = d_modelValues.back();
  for (size_t i=0, nasserts = d_ppAsserts.size(); i<nasserts; i++)
  {
    Node a = d_ppAsserts[i];
    Node av = m->getValue(a);
    av = av.isConst() ? av : Node::null();
    currModel.push_back(av);
    if (av==d_true)
    {
      continue;
    }
    // if its already included in our assertions
    if (d_ainfo.find(i)!=d_ainfo.end())
    {
    }
    if (indexSetToFalse)
    {
      continue;
    }
    if (av==d_false)
    {
      d_nextIndexToInclude = i;
      indexSetToFalse = true;
      indexSet = true;
    }
    else if (!indexSet && av!=d_true)
    {
      
    }
  }
  // we are successful (with SAT) if we didnt set an index
  return !indexSet;
}

}  // namespace smt
}  // namespace cvc5::internal
