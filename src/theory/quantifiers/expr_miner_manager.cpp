/*********************                                                        */
/*! \file expr_miner_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of expression miner manager.
 **/

#include "theory/quantifiers/expr_miner_manager.h"
#include "theory/quantifiers_engine.h"

#include "options/quantifiers_options.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

ExpressionMinerManager::ExpressionMinerManager()
    : d_doRewSynth(false),
      d_doQueryGen(false),
      d_doFilterLogicalStrength(false),
      d_doFilterObjFun(false),
      d_use_sygus_type(false),
      d_qe(nullptr),
      d_tds(nullptr),
      d_crd(options::sygusRewSynthCheck(), options::sygusRewSynthAccel(), false)
{
}

void ExpressionMinerManager::initialize(const std::vector<Node>& vars,
                                        TypeNode tn,
                                        unsigned nsamples,
                                        bool unique_type_ids)
{
  d_doRewSynth = false;
  d_doQueryGen = false;
  d_doFilterLogicalStrength = false;
  d_doFilterObjFun = false;
  d_sygus_fun = Node::null();
  d_use_sygus_type = false;
  d_qe = nullptr;
  d_tds = nullptr;
  // initialize the sampler
  d_sampler.initialize(tn, vars, nsamples, unique_type_ids);
}

void ExpressionMinerManager::initializeSygus(QuantifiersEngine* qe,
                                             Node f,
                                             unsigned nsamples,
                                             bool useSygusType)
{
  d_doRewSynth = false;
  d_doQueryGen = false;
  d_doFilterLogicalStrength = false;
  d_doFilterObjFun = false;
  d_sygus_fun = f;
  d_use_sygus_type = useSygusType;
  d_qe = qe;
  d_tds = qe->getTermDatabaseSygus();
  // initialize the sampler
  d_sampler.initializeSygus(d_tds, f, nsamples, useSygusType);
}

void ExpressionMinerManager::enableRewriteRuleSynth()
{
  if (d_doRewSynth)
  {
    // already enabled
    return;
  }
  d_doRewSynth = true;
  std::vector<Node> vars;
  d_sampler.getVariables(vars);
  // initialize the candidate rewrite database
  if (!d_sygus_fun.isNull())
  {
    Assert(d_qe != nullptr);
    d_crd.initializeSygus(vars, d_qe, d_sygus_fun, &d_sampler);
  }
  else
  {
    d_crd.initialize(vars, &d_sampler);
  }
  d_crd.setExtendedRewriter(&d_ext_rew);
  d_crd.setSilent(false);
}

void ExpressionMinerManager::enableQueryGeneration(unsigned deqThresh)
{
  if (d_doQueryGen)
  {
    // already enabled
    return;
  }
  d_doQueryGen = true;
  std::vector<Node> vars;
  d_sampler.getVariables(vars);
  // must also enable rewrite rule synthesis
  if (!d_doRewSynth)
  {
    // initialize the candidate rewrite database, in silent mode
    enableRewriteRuleSynth();
    d_crd.setSilent(true);
  }
  // initialize the query generator
  d_qg.initialize(vars, &d_sampler);
  d_qg.setThreshold(deqThresh);
}

void ExpressionMinerManager::enableFilterWeakSolutions()
{
  d_doFilterLogicalStrength = true;
  std::vector<Node> vars;
  d_sampler.getVariables(vars);
  d_sols.initialize(vars, &d_sampler);
  d_sols.setLogicallyStrong(true);
}

void ExpressionMinerManager::enableFilterStrongSolutions()
{
  d_doFilterLogicalStrength = true;
  std::vector<Node> vars;
  d_sampler.getVariables(vars);
  d_sols.initialize(vars, &d_sampler);
  d_sols.setLogicallyStrong(false);
}

void ExpressionMinerManager::enableFilterObjFun(const std::vector<Node>& vars,
                                                Node f,
                                                FunDefEvaluator* fde)
{
  d_doFilterObjFun = true;
  d_solObjFun.setObjectiveFunction(vars, f, fde);
}

bool ExpressionMinerManager::addTerm(std::vector<Node>& sols,
                                     std::ostream& out,
                                     bool& rewPrint)
{
  // set the builtin version
  std::vector<Node> solbs = sols;
  if (d_use_sygus_type)
  {
    for (unsigned i = 0, ssize = sols.size(); i < ssize; i++)
    {
      solbs[i] = d_tds->sygusToBuiltin(sols[i]);
    }
  }

  // add to the candidate rewrite rule database
  bool ret = true;
  if (d_doRewSynth)
  {
    Assert (sols.size()==1);
    Node sol = sols[0];
    Node rsol = d_crd.addTerm(sol, options::sygusRewSynthRec(), out, rewPrint);
    ret = (sol == rsol);
  }

  // a unique term, let's try the query generator
  if (ret && d_doQueryGen)
  {
    Assert(solbs.size() == 1);
    d_qg.addTerm(solbs[0], out);
  }

  // filter based on logical strength
  if (ret && d_doFilterLogicalStrength)
  {
    Assert(solbs.size() == 1);
    ret = d_sols.addTerm(solbs[0], out);
  }

  if (ret && d_doFilterObjFun)
  {
    // we use the sygus version
    ret = d_solObjFun.addTerm(sols, out);
  }
  return ret;
}

bool ExpressionMinerManager::addTerm(std::vector<Node>& sols, std::ostream& out)
{
  bool rewPrint = false;
  return addTerm(sols, out, rewPrint);
}

bool ExpressionMinerManager::addTerm(Node sol, std::ostream& out)
{
  bool rewPrint = false;
  return addTerm(sol, out, rewPrint);
}

bool ExpressionMinerManager::addTerm(Node sol,
                                     std::ostream& out,
                                     bool& rewPrint)
{
  std::vector<Node> sols;
  sols.push_back(sol);
  return addTerm(sols, out, rewPrint);
}

const SolutionFilterObjFun& ExpressionMinerManager::getSolutionFilterObjFun()
    const
{
  return d_solObjFun;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
