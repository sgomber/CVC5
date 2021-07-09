/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for constructing and maintaining abstract values.
 */

#include "smt/check_models.h"

#include "base/modal_exception.h"
#include "options/smt_options.h"
#include "options/proof_options.h"
#include "smt/env.h"
#include "smt/model.h"
#include "smt/node_command.h"
#include "smt/preprocessor.h"
#include "smt/smt_solver.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory_engine.h"
#include "theory/smt_engine_subsolver.h"
#include "expr/node_algorithm.h"

using namespace cvc5::theory;

namespace cvc5 {
namespace smt {

CheckModels::CheckModels(Env& e) : d_env(e) {}
CheckModels::~CheckModels() {}

void CheckModels::checkModel(Model* m,
                             context::CDList<Node>* al,
                             bool hardFailure)
{
  // initialize the core checker
  std::unique_ptr<SmtEngine> modelChecker;
  initializeSubsolver(modelChecker);
  modelChecker->getOptions().smt.checkModels = false;
  modelChecker->getOptions().smt.checkUnsatCores = false;
  // disable all proof options
  modelChecker->getOptions().smt.produceProofs = false;
  modelChecker->getOptions().smt.checkProofs = false;
  modelChecker->getOptions().proof.proofEagerChecking = false;
  // set up separation logic heap if necessary
  /*
  TypeNode sepLocType, sepDataType;
  if (getSepHeapTypes(sepLocType, sepDataType))
  {
    modelChecker->declareSepHeap(sepLocType, sepDataType);
  }
  */
  Trace("check-models") << "SmtEngine::checkModels(): pushing core assertions"
           << std::endl;
  theory::SubstitutionMap& sm = d_env.getTopLevelSubstitutions().get();
  std::unordered_set<Node> syms;
  for (const Node& assertion : *al) {
    expr::getSymbols(assertion, syms);
    Trace("check-models") << "SmtEngine::checkModels(): pushing assertion " << assertion << "\n";
    modelChecker->assertFormula(assertion);
  }
  for (const Node& s : syms)
  {
    Trace("check-models") << "SmtEngine::checkModels(): define symbol " << s << "\n";
    Node sv = m->getValue(s);
    Trace("check-models") << "Define as " << sv << std::endl;
    Node val = sv;
    std::vector<Node> formals;
    if (sv.getKind()==kind::LAMBDA)
    {
      formals.insert(formals.end(), sv[0].begin(), sv[0].end());
      val = sv[1];
    }
    modelChecker->defineFunction(s, formals, val, false);
  }
  Result r;
  try {
    r = modelChecker->checkSat();
  } catch(...) {
    throw;
  }
  Trace("check-models") << "SmtEngine::checkModels(): result is " << r << std::endl;
  if(r.asSatisfiabilityResult().isUnknown()) {
    Warning()
        << "SmtEngine::checkModels(): could not check core result unknown."
        << std::endl;
  }
  else if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    InternalError()
        << "SmtEngine::checkModels(): produced model assertions were unsatisfiable.";
  }
  return;
  
  
  // Throughout, we use Notice() to give diagnostic output.
  //
  // If this function is running, the user gave --check-model (or equivalent),
  // and if Notice() is on, the user gave --verbose (or equivalent).

  // check-model is not guaranteed to succeed if approximate values were used.
  // Thus, we intentionally abort here.
  if (m->hasApproximations())
  {
    throw RecoverableModalException(
        "Cannot run check-model on a model with approximate values.");
  }

  Trace("check-model") << "checkModel: Check assertions..." << std::endl;
  std::unordered_map<Node, Node> cache;
  // the list of assertions that did not rewrite to true
  std::vector<Node> noCheckList;
  // Now go through all our user assertions checking if they're satisfied.
  for (const Node& assertion : *al)
  {
    Notice() << "SmtEngine::checkModel(): checking assertion " << assertion
             << std::endl;

    // Apply any define-funs from the problem. We do not expand theory symbols
    // like integer division here. Hence, the code below is not able to properly
    // evaluate e.g. divide-by-zero. This is intentional since the evaluation
    // is not trustworthy, since the UF introduced by expanding definitions may
    // not be properly constrained.
    Node n = sm.apply(assertion, false);
    Notice() << "SmtEngine::checkModel(): -- substitutes to " << n << std::endl;

    n = Rewriter::rewrite(n);
    Notice() << "SmtEngine::checkModel(): -- rewrites to " << n << std::endl;

    // We look up the value before simplifying. If n contains quantifiers,
    // this may increases the chance of finding its value before the node is
    // altered by simplification below.
    n = m->getValue(n);
    Notice() << "SmtEngine::checkModel(): -- get value : " << n << std::endl;

    if (n.isConst() && n.getConst<bool>())
    {
      // assertion is true, everything is fine
      continue;
    }

    // Otherwise, we did not succeed in showing the current assertion to be
    // true. This may either indicate that our model is wrong, or that we cannot
    // check it. The latter may be the case for several reasons.
    // For example, quantified formulas are not checkable, although we assign
    // them to true/false based on the satisfying assignment. However,
    // quantified formulas can be modified during preprocess, so they may not
    // correspond to those in the satisfying assignment. Hence we throw
    // warnings for assertions that do not simplify to either true or false.
    // Other theories such as non-linear arithmetic (in particular,
    // transcendental functions) also have the property of not being able to
    // be checked precisely here.
    // Note that warnings like these can be avoided for quantified formulas
    // by making preprocessing passes explicitly record how they
    // rewrite quantified formulas (see cvc4-wishues#43).
    if (!n.isConst())
    {
      // Not constant, print a less severe warning message here.
      Warning() << "Warning : SmtEngine::checkModel(): cannot check simplified "
                   "assertion : "
                << n << std::endl;
      noCheckList.push_back(n);
      continue;
    }
    // Assertions that simplify to false result in an InternalError or
    // Warning being thrown below (when hardFailure is false).
    Notice() << "SmtEngine::checkModel(): *** PROBLEM: EXPECTED `TRUE' ***"
             << std::endl;
    std::stringstream ss;
    ss << "SmtEngine::checkModel(): "
       << "ERRORS SATISFYING ASSERTIONS WITH MODEL:" << std::endl
       << "assertion:     " << assertion << std::endl
       << "simplifies to: " << n << std::endl
       << "expected `true'." << std::endl
       << "Run with `--check-models -v' for additional diagnostics.";
    if (hardFailure)
    {
      // internal error if hardFailure is true
      InternalError() << ss.str();
    }
    else
    {
      Warning() << ss.str() << std::endl;
    }
  }
  if (noCheckList.empty())
  {
    Notice() << "SmtEngine::checkModel(): all assertions checked out OK !"
             << std::endl;
    return;
  }
  // if the noCheckList is non-empty, we could expand definitions on this list
  // and check satisfiability

  Trace("check-model") << "checkModel: Finish" << std::endl;
}

}  // namespace smt
}  // namespace cvc5
