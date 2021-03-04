/*********************                                                        */
/*! \file solution_filter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for filtering solutions.
 **/

#include "theory/quantifiers/solution_filter.h"

#include <fstream>
#include "options/quantifiers_options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "util/random.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SolutionFilterStrength::SolutionFilterStrength() : d_isStrong(true) {}
void SolutionFilterStrength::initialize(const std::vector<Node>& vars,
                                        SygusSampler* ss)
{
  ExprMiner::initialize(vars, ss);
}

void SolutionFilterStrength::setLogicallyStrong(bool isStrong)
{
  d_isStrong = isStrong;
}

bool SolutionFilterStrength::addTerm(Node n, std::ostream& out)
{
  if (!n.getType().isBoolean())
  {
    // currently, should not register non-Boolean terms here
    Assert(false);
    return true;
  }
  Node basen = d_isStrong ? n : n.negate();
  NodeManager* nm = NodeManager::currentNM();
  // Do i subsume the disjunction of all previous solutions? If so, we discard
  // this immediately
  Node curr;
  if (!d_curr_sols.empty())
  {
    curr = d_curr_sols.size() == 1
               ? d_curr_sols[0]
               : nm->mkNode(d_isStrong ? OR : AND, d_curr_sols);
    Node imp = nm->mkNode(AND, basen.negate(), curr);
    Trace("sygus-sol-implied")
        << "  implies: check subsumed (strong=" << d_isStrong << ") " << imp
        << "..." << std::endl;
    // check the satisfiability query
    Result r = doCheck(imp);
    Trace("sygus-sol-implied") << "  implies: ...got : " << r << std::endl;
    if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      // it is subsumed by the current, discard this
      return false;
    }
  }
  // check which solutions would have been filtered if the current had come
  // first
  if (options::sygusFilterSolRevSubsume())
  {
    std::vector<Node> nsubsume;
    for (const Node& s : d_curr_sols)
    {
      Node imp = nm->mkNode(AND, s.negate(), basen);
      Trace("sygus-sol-implied")
          << "  implies: check subsuming " << imp << "..." << std::endl;
      // check the satisfiability query
      Result r = doCheck(imp);
      Trace("sygus-sol-implied") << "  implies: ...got : " << r << std::endl;
      if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
      {
        nsubsume.push_back(s);
      }
      else
      {
        Options& opts = smt::currentSmtEngine()->getOptions();
        std::ostream* smtOut = opts.getOut();
        (*smtOut) << "; (filtered " << (d_isStrong ? s : s.negate()) << ")"
                  << std::endl;
      }
    }
    d_curr_sols.clear();
    d_curr_sols.insert(d_curr_sols.end(), nsubsume.begin(), nsubsume.end());
  }
  d_curr_sols.push_back(basen);
  return true;
}

void SolutionFilterObjFun::setObjectiveFunction(const std::vector<Node>& vars,
                                                Node f,
                                                FunDefEvaluator* fde)
{
  d_objFunVars = vars;
  // expand definitions
  d_objFun =
      Node::fromExpr(smt::currentSmtEngine()->expandDefinitions(f.toExpr()));
  d_funDefEval = fde;
  // must be real valued
  AlwaysAssert(d_objFun.getType().isReal());
}

bool SolutionFilterObjFun::addTerm(Node n, std::ostream& out)
{
  std::vector<Node> sols;
  sols.push_back(n);
  return addTerm(sols, out);
}

bool SolutionFilterObjFun::addTerm(std::vector<Node>& sols, std::ostream& out)
{
  Trace("sygus-filter-obj-fun-debug")
      << "Filter via objective function: " << sols << std::endl;
  Assert(sols.size() == d_objFunVars.size());
  Node res = d_eval.eval(d_objFun, d_objFunVars, sols);
  if (res.isNull())
  {
    Trace("sygus-filter-obj-fun-debug") << "...must substitute" << std::endl;
    res = d_objFun.substitute(
        d_objFunVars.begin(), d_objFunVars.end(), sols.begin(), sols.end());
    res = Rewriter::rewrite(res);
  }
  if (!res.isConst())
  {
    if (d_funDefEval != nullptr)
    {
      res = d_funDefEval->evaluate(res);
    }
    if (!res.isConst())
    {
      Trace("sygus-filter-obj-fun")
          << "Value of objective function is non-constant " << res << std::endl;
      // not constant, must keep but don't set value
      Trace("sygus-filter-obj-fun") << "...keep (non-constant)" << std::endl;
      return true;
    }
  }
  Trace("sygus-filter-obj-fun")
      << "Value of objective function is " << res << std::endl;
  bool retValue = false;
  if (d_maxValue.isNull())
  {
    d_maxValue = res;
    retValue = true;
    Trace("sygus-filter-obj-fun") << "...keep (first)" << std::endl;
  }
  else if (res.getConst<Rational>() > d_maxValue.getConst<Rational>())
  {
    d_maxValue = res;
    retValue = true;
    Trace("sygus-filter-obj-fun") << "...keep (new max)" << std::endl;
  }
  if (retValue)
  {
    out << "; optimal value is now " << d_maxValue << std::endl;
  }
  return retValue;
}

Node SolutionFilterObjFun::getCurrentMaxValue() const { return d_maxValue; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
