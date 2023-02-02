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

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "smt/smt_solver.h"
#include "theory/theory_engine.h"
#include "theory/smt_engine_subsolver.h"

namespace cvc5::internal {
namespace smt {

SmtDriverAbstractRefine::SmtDriverAbstractRefine(Env& env,
                                                 SmtSolver& smt,
                                                 ContextManager* ctx)
    : SmtDriver(env, smt, ctx), d_initialized(false)
{
}

Result SmtDriverAbstractRefine::checkSatNext(
    preprocessing::AssertionPipeline& ap)
{
  d_smt.preprocess(ap);
  d_smt.assertToInternal(ap);
  Trace("smt-abs-refine") << "SmtDriverAbstractRefine::checkSatNext" << std::endl;
  Result result = d_smt.checkSatInternal();
  Trace("smt-abs-refine") << "...returns " << result << std::endl;
  // check again if we didn't solve and there are learned literals
  if (result.getStatus() != Result::UNSAT)
  {
    return checkResult(result);
  }
  return result;
}

void SmtDriverAbstractRefine::getNextAssertions(
    preprocessing::AssertionPipeline& ap)
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
    Trace("smt-abs-refine")
        << "SmtDriverAbstractRefine: initialize with " << d_avarToTerm.size()
        << " variables." << std::endl;
  }
  // take all assertions
  for (const Node& a : d_currAssertions)
  {
    ap.push_back(a, true);
  }
}

Node SmtDriverAbstractRefine::booleanAbstractionOf(const Node& n)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    Assert (cur.getType().isBoolean());
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      if (cur.isConst() || cur.isVar())
      {
        visited[cur] = cur;
      }
      else if (!expr::isBooleanConnective(cur))
      {
        visited[cur] = getAbstractionVariableFor(cur);
      }
      else
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Result SmtDriverAbstractRefine::checkResult(const Result& result)
{
  Trace("smt-abs-refine") << "SmtDriverAbstractRefine::checkResult: " << result << std::endl;
  bool success;
  std::unordered_set<TNode> rasserts =
      d_smt.getTheoryEngine()->getRelevantAssertions(success);
  // maybe all assertions are not abstracted? if so, we are truly SAT
  if (!success)
  {
      Trace("smt-abs-refine") << "...return unknown (failed to get relevant assertions)" << std::endl;
    // failed to
    return Result(Result::UNKNOWN);
  }
  bool wasAbstract = false;
  // change to concrete form
  std::vector<Node> query;
  std::map<Node, Node>::iterator it;
  for (TNode a : rasserts)
  {
    bool apol = a.getKind()!=kind::NOT;
    Node atom = apol ? a : a[0];
    it = d_avarToTerm.find(atom);
    if (it != d_avarToTerm.end())
    {
      wasAbstract = true;
      query.push_back(apol ? it->second : it->second.notNode());
    }
    else if (d_elimAVar.find(a)==d_elimAVar.end())
    {
      query.push_back(a);
    }
  }
  // also take substitutions
  const theory::SubstitutionMap& sm = d_env.getTopLevelSubstitutions().get();
  const std::unordered_map<Node, Node>& ss = sm.getSubstitutions();
  for (const std::pair<const Node, Node>& s : ss)
  {
    // abstraction variable in a top-level substitution
    it = d_avarToTerm.find(s.first);
    if (it != d_avarToTerm.end())
    {
      wasAbstract = true;
      query.push_back(s.second.getConst<bool>() ? it->second : it->second.notNode());
    }
  }
  if (!wasAbstract)
  {
      Trace("smt-abs-refine") << "...return sat (concrete assignment from main solver)" << std::endl;
    // if nothing was abstract, return SAT
    return Result(Result::SAT);
  }

  if (TraceIsOn("smt-abs-refine"))
  {
    Trace("smt-abs-refine")
        << "Check result with relevant assertions:" << std::endl;
    for (const Node& a : query)
    {
      Trace("smt-abs-refine") << "- " << a << std::endl;
    }
  }
  // check the conjunction separately
  std::unique_ptr<SolverEngine> checkAssignment;
  theory::initializeSubsolver(checkAssignment, d_env);
  checkAssignment->setOption("produce-unsat-cores", "true");
  checkAssignment->setOption("smt-abs-refine", "false");
  for (const Node& a : query)
  {
    checkAssignment->assertFormula(a);
  }
  Result rsub = checkAssignment->checkSat();
  Trace("smt-abs-refine") << "...result: " << rsub << std::endl;
  if (rsub.getStatus()==Result::SAT)
  {
    // the concrete version is SAT, we are done
    Trace("smt-abs-refine") << "...return SAT (from subsolver)" << std::endl;
    return rsub;
  }
  if (rsub.getStatus()==Result::UNSAT)
  {
    // get the unsat core and unabstract those in the unsat core
    std::vector<Node> uasserts;
    theory::getUnsatCoreFromSubsolver(*checkAssignment.get(), uasserts);
    // take the literals in the unsat core that were abstracted and permanently
    // concretize them
    Subs subs;
    Trace("smt-abs-refine") << "Unsat core: " << std::endl;
    for (const Node& u : uasserts)
    {
      Trace("smt-abs-refine") << "- " << u;
      Node atom = u.getKind()==kind::NOT ? u[0] : u;
      it = d_termToAVar.find(atom);
      if (it!=d_termToAVar.end())
      {
        Trace("smt-abs-refine") << ", corresponding to " << it->second;
        subs.add(it->second, atom);
        d_elimAVar.insert(it->second);
        d_avarToTerm.erase(it->second);
        d_termToAVar.erase(it);
      }
      Trace("smt-abs-refine") << std::endl;
    }
    if (subs.empty())
    {
      Trace("smt-abs-refine") << "...return unknown (no refinement from unsat core)" << std::endl;
      // In a strange case where we constructed an unsat core that was
      // not refuted in the main solver. In this case, we give up
      Assert (result.getStatus()==Result::UNKNOWN);
      return Result(Result::UNKNOWN);
    }
    // apply the substitution to the current assertions
    for (Node& a : d_currAssertions)
    {
      a = subs.apply(a);
    }
    Trace("smt-abs-refine") << "...return check again" << std::endl;
    return Result(Result::UNKNOWN, REQUIRES_CHECK_AGAIN);
  }
  Trace("smt-abs-refine") << "...return unknown (from subsolver)" << std::endl;
  Assert (rsub.getStatus()==Result::UNKNOWN);
  return rsub;
}

Node SmtDriverAbstractRefine::getAbstractionVariableFor(const Node& n)
{
  std::map<Node, Node>::iterator it = d_termToAVar.find(n);
  if (it != d_termToAVar.end())
  {
    return it->second;
  }
  SkolemManager* skm = NodeManager::currentNM()->getSkolemManager();
  Node k = skm->mkDummySkolem("av", n.getType());
  d_termToAVar[n] = k;
  d_avarToTerm[k] = n;
  return k;
}

}  // namespace smt
}  // namespace cvc5::internal
