/*********************                                                        */
/*! \file sygus_qe_preproc.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus quantifier elimination preprocessor
 **/

#include "theory/quantifiers/sygus/sygus_qe_preproc.h"

#include "expr/node_algorithm.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/single_inv_partition.h"
#include "theory/quantifiers/sygus/sygus_utils.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusQePreproc::SygusQePreproc(QuantifiersEngine* qe) {}

Node SygusQePreproc::preprocess(Node q)
{
  Trace("cegqi-qep") << "SygusQePreproc::preprocess: " << q << std::endl;
  // decompose the conjecture into solved, unsolved components
  std::vector<Node> allf;
  std::vector<Node> unsf;
  Subs solvedf;
  decomposeSygusConjecture(q, allf, unsf, solvedf);
  if (unsf.empty())
  {
    // probably should never happen
    Trace("cegqi-qep") << "...fully solved, success." << std::endl;
    return Node::null();
  }

  // Get the functions that we would be applying single invocation for, which
  // are the functions of maximal arity having the same type.
  std::vector<Node> maxf;
  Subs remf;
  Subs xf;
  std::vector<Node> xargs;
  if (!getMaximalArityFuncs(unsf, maxf, remf, xf, xargs))
  {
    // arity mismatch for functions, we are done
    Trace("cegqi-qep") << "...max arity type mismatch, fail." << std::endl;
    return Node::null();
  }

  Trace("cegqi-qep-debug") << "Compute single invocation for " << q << "..."
                           << std::endl;
  SingleInvocationPartition sip;
  Node body = q[1];
  if (body.getKind() == NOT && body[0].getKind() == FORALL)
  {
    body = body[0][1];
  }
  Trace("cegqi-qep-debug") << "Max function variables = " << maxf << std::endl;
  Trace("cegqi-qep-debug") << "Body processed to " << body << std::endl;
  // skolemize free symbols
  Subs remk;
  remk.add(remf.d_vars);
  body = remk.apply(body);
  // initialize the single invocation utility
  sip.init(maxf, body);
  Trace("cegqi-qep-debug") << "Computed single invocation:" << std::endl;
  sip.debugPrint("cegqi-qep-debug");
  // if not all functions are of maximal arity, we will try to rewrite
  if (!remf.empty())
  {
    Node bodyNorm = sip.getFullSpecification();
    // revert the skolemization of other functions
    bodyNorm = remk.rapply(bodyNorm);
    Trace("cegqi-qep-debug")
        << "Nested process, full specification:" << bodyNorm << std::endl;
    std::vector<Node> siVars;
    sip.getSingleInvocationVariables(siVars);
    Trace("cegqi-qep-debug")
        << "Single invocation variables:" << siVars << std::endl;
    // rewrite for the normalized arguments
    Subs siToXArgs;
    siToXArgs.add(xargs, siVars);
    siToXArgs.applyToRange(remf);
    // substitute the body { remf -> rems }
    bodyNorm = remf.apply(bodyNorm);
    bodyNorm = Rewriter::rewrite(bodyNorm);
    Trace("cegqi-qep-debug")
        << "Extended and normalized:" << bodyNorm << std::endl;
    // compute single invocation, again, with maxf + extended argument functions
    SingleInvocationPartition sipxf;
    std::vector<Node> xmaxf = maxf;
    xmaxf.insert(xmaxf.end(), xf.d_vars.begin(), xf.d_vars.end());

    sipxf.init(xmaxf, bodyNorm);
    Trace("cegqi-qep-debug")
        << "Computed single invocation (after expansion):" << std::endl;
    sipxf.debugPrint("cegqi-qep-debug");
    if (sipxf.isPurelySingleInvocation())
    {
      Trace("cegqi-qep") << "...eliminate functions." << std::endl;
      // solve for a subset of the functions
      Node ret = eliminateFunctions(q, allf, maxf, xf, solvedf, sipxf);
      Trace("cegqi-qep") << "...eliminate functions returned " << ret
                         << std::endl;
      return ret;
    }
    // otherwise, does it matter?
  }

  if (sip.isPurelySingleInvocation())
  {
    Trace("cegqi-qep") << "...pure single invocation, success." << std::endl;
    return Node::null();
  }

  if (!sip.isNonGroundSingleInvocation())
  {
    // property is not single invocation, fail
    Trace("cegqi-qep") << "...not non-ground single invocation, fail."
                       << std::endl;
    return Node::null();
  }
  Trace("cegqi-qep") << "...eliminate variables." << std::endl;
  // non-ground single invocation, eliminate variables
  Node ret = eliminateVariables(q, allf, maxf, xf, solvedf, sip);
  Trace("cegqi-qep") << "...eliminate variables returned " << ret << std::endl;
  return ret;
}

Node SygusQePreproc::eliminateVariables(Node q,
                                        const std::vector<Node>& allf,
                                        const std::vector<Node>& maxf,
                                        const Subs& xf,
                                        Subs& solvedf,
                                        SingleInvocationPartition& sip)
{
  NodeManager* nm = NodeManager::currentNM();
  // create new smt engine to do quantifier elimination
  std::unique_ptr<SmtEngine> smt_qe;
  initializeSubsolver(smt_qe);
  Trace("cegqi-qep-debug") << "Property is non-ground single invocation, run "
                              "QE to obtain single invocation."
                           << std::endl;
  // partition variables
  std::vector<Node> all_vars;
  sip.getAllVariables(all_vars);
  std::vector<Node> si_vars;
  sip.getSingleInvocationVariables(si_vars);
  std::vector<Node> qe_vars;
  std::vector<Node> nqe_vars;
  for (const Node& v : all_vars)
  {
    if (std::find(maxf.begin(), maxf.end(), v) != maxf.end())
    {
      Trace("cegqi-qep-debug") << "- fun var: " << v << std::endl;
    }
    else if (std::find(si_vars.begin(), si_vars.end(), v) == si_vars.end())
    {
      qe_vars.push_back(v);
      Trace("cegqi-qep-debug") << "- qe var: " << v << std::endl;
    }
    else
    {
      nqe_vars.push_back(v);
      Trace("cegqi-qep-debug") << "- non qe var: " << v << std::endl;
    }
  }
  // substitution from functions to skolems
  Subs origSubs;
  // skolemize non-qe variables
  origSubs.add(nqe_vars);
  // skolemize the other functions
  std::vector<Node> funcs1;
  sip.getFunctions(funcs1);
  for (const Node& f : funcs1)
  {
    Node fi = sip.getFunctionInvocationFor(f);
    Assert(!fi.isNull());
    origSubs.add(fi);
  }

  Node conj_se_ngsi = sip.getFullSpecification();
  Trace("cegqi-qep-debug") << "Full specification is " << conj_se_ngsi
                           << std::endl;
  Node conj_se_ngsi_subs = origSubs.apply(conj_se_ngsi);
  Assert(!qe_vars.empty());
  conj_se_ngsi_subs = nm->mkNode(
      EXISTS, nm->mkNode(BOUND_VAR_LIST, qe_vars), conj_se_ngsi_subs.negate());

  Trace("cegqi-qep-debug") << "Run quantifier elimination on "
                           << conj_se_ngsi_subs << std::endl;
  Node qeRes = smt_qe->getQuantifierElimination(conj_se_ngsi_subs, true, false);
  Trace("cegqi-qep-debug") << "Result : " << qeRes << std::endl;

  // create single invocation conjecture, if QE was successful
  if (!expr::hasBoundVar(qeRes))
  {
    qeRes = origSubs.rapply(qeRes);
    // must additionally map back to original functions
    qeRes = xf.apply(qeRes);
    if (!nqe_vars.empty())
    {
      qeRes = nm->mkNode(EXISTS, nm->mkNode(BOUND_VAR_LIST, nqe_vars), qeRes);
    }
    Assert(q.getNumChildren() == 3);
    // use mkConjecture, which carries the solved information
    qeRes = mkSygusConjecture(allf, qeRes, solvedf);
    Trace("cegqi-qep-debug")
        << "Converted conjecture after QE : " << qeRes << std::endl;
    qeRes = Rewriter::rewrite(qeRes);
    return qeRes;
  }
  return Node::null();
}

Node SygusQePreproc::eliminateFunctions(Node q,
                                        const std::vector<Node>& allf,
                                        const std::vector<Node>& maxf,
                                        const Subs& xf,
                                        Subs& solvedf,
                                        SingleInvocationPartition& sip)
{
  NodeManager* nm = NodeManager::currentNM();
  // use the specification from the single invocation partition utility
  Node bodyNorm = sip.getFullSpecification();
  Trace("cegqi-qep-debug") << "Full specification is " << bodyNorm << std::endl;

  // eliminate the conjuncts that do not contain some function in maxf
  std::vector<Node> bnconj;
  if (bodyNorm.getKind() == AND)
  {
    bnconj.insert(bnconj.end(), bodyNorm.begin(), bodyNorm.end());
  }
  else
  {
    bnconj.push_back(bodyNorm);
  }
  std::vector<Node> bnconjc;
  for (const Node& bnc : bnconj)
  {
    if (expr::hasSubterm(bnc, maxf))
    {
      bnconjc.push_back(bnc);
    }
  }
  bodyNorm = nm->mkAnd(bnconjc);
  Trace("cegqi-qep-debug") << "...after miniscope: " << bodyNorm << std::endl;

  // skolemize the functions that we are not solving
  Subs xfk;
  for (const Node& v : xf.d_vars)
  {
    Node fi = sip.getFunctionInvocationFor(v);
    Assert(!fi.isNull());
    xfk.add(fi);
  }
  bodyNorm = xfk.apply(bodyNorm);
  Trace("cegqi-qep-debug") << "After skolemizing: " << bodyNorm << std::endl;

  std::vector<Node> siVars;
  sip.getSingleInvocationVariables(siVars);

  Trace("cegqi-qep-debug") << "Free variables: " << siVars << std::endl;

  // create new smt engine to do sygus
  std::unique_ptr<SmtEngine> smt_sy;
  initializeSubsolver(smt_sy);

  // functions-to-synthesize, keep the same formal argument list
  for (const Node& f : maxf)
  {
    std::vector<Node> formals;
    getSygusArgumentListForSynthFun(f,formals);
    smt_sy->declareSynthFun(f, false, formals);
  }

  for (const Node& v : siVars)
  {
    smt_sy->declareSygusVar(v);
  }
  // assert the sygus constraint
  smt_sy->assertSygusConstraint(bodyNorm);

  Result r = smt_sy->checkSynth();
  Trace("sygus-qep-debug") << "eliminateFunctions result: " << r << std::endl;
  if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    std::map<Node, Node> solMap;
    smt_sy->getSynthSolutions(solMap);
    Subs solSubs;
    for (const std::pair<const Node, Node>& sol : solMap)
    {
      solSubs.add(sol.first, sol.second);
    }
    Trace("sygus-qep-debug") << "Solution : " << solSubs << std::endl;
    // undo the skolemization of the extended functions
    xfk.rapplyToRange(solSubs);
    Trace("sygus-qep-debug")
        << "...after unskolemize : " << solSubs << std::endl;
    // extended functions have a definition in terms of the originals
    xf.rapplyToRange(solSubs);
    Trace("sygus-qep-debug")
        << "...after revert extensions : " << solSubs << std::endl;
    Trace("sygus-qep-debug")
        << "Previous solution set : " << solvedf << std::endl;
    // solSubs are correct, now update previous solutions
    solSubs.applyToRange(solvedf);
    Trace("sygus-qep-debug") << "...updated to : " << solvedf << std::endl;
    // now append new solutions to solved
    solvedf.append(solSubs);

    // get the original conjecture and update it with the new solutions
    Node conjfs = solSubs.apply(q[1]);

    // reconstruct the new conjecture
    Node fsRes = mkSygusConjecture(allf, conjfs, solvedf);
    fsRes = Rewriter::rewrite(fsRes);
    return fsRes;
  }

  return Node::null();
}

bool SygusQePreproc::getMaximalArityFuncs(const std::vector<Node>& unsf,
                                          std::vector<Node>& maxf,
                                          Subs& remf,
                                          Subs& xf,
                                          std::vector<Node>& xargs)
{
  Assert(!unsf.empty());
  NodeManager* nm = NodeManager::currentNM();
  size_t maxArity = 0;
  TypeNode maxType;
  bool maxArityValid = true;
  for (const Node& f : unsf)
  {
    TypeNode tn = f.getType();
    size_t arity = tn.isFunction() ? tn.getNumChildren() - 1 : 0;
    Trace("cegqi-qep-debug")
        << "Arity(" << f << ")=" << arity << ", type = " << tn << std::endl;
    if (arity > maxArity)
    {
      maxArity = arity;
      maxArityValid = true;
      maxType = tn;
    }
    else if (arity == maxArity)
    {
      if (maxType.isNull())
      {
        maxArityValid = true;
        maxType = tn;
      }
      else if (maxType != tn)
      {
        // maximal arity function is currently invalid
        maxArityValid = false;
      }
    }
  }
  if (!maxArityValid)
  {
    return false;
  }
  std::vector<TypeNode> maxTypeArgs;
  if (maxType.isFunction())
  {
    maxTypeArgs = maxType.getArgTypes();
    for (const TypeNode& mta : maxTypeArgs)
    {
      xargs.push_back(nm->mkBoundVar(mta));
    }
  }
  // deompose into maximal arity functions and remaining functions
  for (const Node& f : unsf)
  {
    TypeNode tn = f.getType();
    if (tn == maxType)
    {
      maxf.push_back(f);
      continue;
    }
    // extend it to the proper type
    if (!extendFuncArgs(f, xargs, remf, xf))
    {
      return false;
    }
  }
  return true;
}

bool SygusQePreproc::extendFuncArgs(Node f,
                                    const std::vector<Node>& xargs,
                                    Subs& remf,
                                    Subs& xf)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(!xargs.empty());
  TypeNode tn = f.getType();
  std::vector<TypeNode> domainTs;
  TypeNode rangeT = tn;
  if (tn.isFunction())
  {
    domainTs = tn.getArgTypes();
    rangeT = tn.getRangeType();
  }
  Assert(domainTs.size() < xargs.size());
  // argument must be a prefix, generalizations of this should deal with
  // argument order separately.
  std::vector<Node> args;
  for (size_t i = 0, ndts = domainTs.size(); i < ndts; i++)
  {
    if (domainTs[i] != xargs[i].getType())
    {
      // not a prefix
      return false;
    }
    args.push_back(nm->mkBoundVar(domainTs[i]));
  }
  Node lbvl;
  if (!args.empty())
  {
    lbvl = nm->mkNode(BOUND_VAR_LIST, args);
  }
  // Add the pair
  //   f, (lambda ((x domainTs)) (newF x xargs2))
  // to remf, where the latter term has the same type as f.
  std::vector<TypeNode> fargs;
  for (const Node& xa : xargs)
  {
    fargs.push_back(xa.getType());
  }
  TypeNode newT = nm->mkFunctionType(fargs, rangeT);
  Node newF = nm->mkSkolem("xf", newT);
  for (size_t i = args.size(), nfargs = fargs.size(); i < nfargs; i++)
  {
    args.push_back(xargs[i]);
  }
  args.insert(args.begin(), newF);
  Node app = nm->mkNode(APPLY_UF, args);
  Node lam = lbvl.isNull() ? app : nm->mkNode(LAMBDA, lbvl, app);
  Assert(f.getType() == lam.getType());
  remf.add(f, lam);
  Trace("cegqi-qep-debug") << "extendFuncArgs: Extend: " << f << " -> " << lam
                           << std::endl;
  // also make the reverse mapping
  //   newF, (lambda (xargs1 xargs2) (f xargs1))
  // to xf, where the latter term has the same type as newF.
  std::vector<Node> argsf;
  argsf.push_back(f);
  argsf.insert(argsf.end(), args.begin(), args.begin() + domainTs.size());
  args.erase(args.begin(), args.begin() + 1);
  lbvl = nm->mkNode(BOUND_VAR_LIST, args);
  app = nm->mkNode(APPLY_UF, argsf);
  lam = nm->mkNode(LAMBDA, lbvl, app);
  Trace("cegqi-qep-debug") << "extendFuncArgs: Restrict: " << newF << " -> "
                           << lam << std::endl;
  xf.add(newF, lam);
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
