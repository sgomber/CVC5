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
#include "theory/quantifiers/sygus/sygus_utils_si.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Node SygusQePreproc::preprocess(Node q)
{
  Trace("sygus-qep") << "SygusQePreproc::preprocess: " << q << std::endl;
  // decompose the conjecture into solved, unsolved components
  std::vector<Node> allf;
  std::vector<Node> unsf;
  Subs solvedf;
  decomposeSygusConjecture(q, allf, unsf, solvedf);
  if (unsf.empty())
  {
    // probably should never happen
    Trace("sygus-qep") << "...fully solved, success." << std::endl;
    return Node::null();
  }
  Trace("sygus-qep-debug") << "- functions = " << allf << std::endl;
  Trace("sygus-qep-debug") << "- init unsolved = " << unsf << std::endl;
  Trace("sygus-qep-debug") << "- init solved = " << solvedf << std::endl;

  // Get the functions that we would be applying single invocation for, which
  // are the functions of maximal arity having the same type.
  std::vector<Node> maxf;
  if (!getMaximalArityFuncs(unsf, maxf))
  {
    // arity mismatch for functions, we are done
    Trace("sygus-qep") << "...max arity type mismatch, fail." << std::endl;
    return Node::null();
  }
  Trace("sygus-qep-debug") << "- max arity functions = " << maxf << std::endl;

  std::vector<Node> args;
  Trace("sygus-qep-debug") << "Check single invocation " << maxf << ": " << q[1]
                           << std::endl;
  if (!isSingleInvocation(maxf, q[1], args))
  {
    Trace("sygus-qep")
        << "...not single invocation with respect to max arity functions"
        << std::endl;
    // not single invocation
    return Node::null();
  }
  Trace("sygus-qep-debug") << "...single invocation with args = " << args
                           << std::endl;
  // Get the remaining functions. We also compute methods for extending
  // them to extended functions in xf. The substitutions remf converts the
  // remaining functions to extended ones (with the same type as maxf), and
  // the map xf converts the extended functions back to the originals.
  Subs remf;
  Subs xf;
  Node xbody = q[1];
  if (maxf.size() < allf.size())
  {
    // more generally, need all single invocations
    std::map<Node, std::vector<Node>> rargs;
    getSingleInvocations(allf, q[1], rargs);
    if (!getRemainingFunctions(unsf, maxf, remf, xf, args, rargs))
    {
      // arity mismatch for functions, we are done
      Trace("sygus-qep") << "...remaining arity type mismatch, fail."
                         << std::endl;
      return Node::null();
    }
    Trace("sygus-qep-debug")
        << "- remaining-to-extension = " << remf << std::endl;
    Trace("sygus-qep-debug")
        << "- extension-to-remaining = " << xf << std::endl;

    // lift remaining functions to extended functions
    xbody = remf.apply(q[1], true);
    Trace("sygus-qep-debug")
        << "Extended and normalized body:" << xbody << std::endl;
  }
  // Check single invocation with respect to the extension. Note this is
  // computed regardless of whether we changed xmaxf for uniformity.
  std::vector<Node> xmaxf = maxf;
  xmaxf.insert(xmaxf.end(), xf.d_vars.begin(), xf.d_vars.end());
  std::map<Node, Node> xffs;
  std::vector<Node> xargs;
  Trace("sygus-qep-debug") << "Check single invocation " << xmaxf << ": "
                           << xbody << std::endl;
  if (!isSingleInvocation(xmaxf, xbody, xffs, xargs))
  {
    Trace("sygus-qep") << "...not single invocation after extension"
                       << std::endl;
    // not single invocation
    return Node::null();
  }
  Assert(args.size() == xargs.size());
  Trace("sygus-qep-debug") << "...extended single invocation with args = "
                           << xargs << std::endl;

  // decompose the body of the synthesis conjecture
  Node body = xbody;
  std::vector<Node> uvars;
  Node qfBody = decomposeConjectureBody(body, uvars);

  NodeManager* nm = NodeManager::currentNM();

  // ===== A: if there free variables apart from args, do quantifier elimination
  if (uvars.size() > xargs.size())
  {
    Subs xmaxfk;
    xmaxfk.add(xargs);
    std::vector<Node> qevars;
    for (const Node& v : body[0][0])
    {
      if (std::find(xargs.begin(), xargs.end(), v) == xargs.end())
      {
        qevars.push_back(v);
      }
    }
    Assert(!qevars.empty());
    std::map<Node, Node>::iterator itf;
    for (const Node& x : xmaxf)
    {
      itf = xffs.find(x);
      if (itf != xffs.end())
      {
        // will substitute function invocation by fresh skolem
        xmaxfk.add(itf->second);
      }
    }
    Node conj = xmaxfk.apply(qfBody);
    Node ebvl = nm->mkNode(BOUND_VAR_LIST, qevars);
    Node qeconj = nm->mkNode(EXISTS, ebvl, conj.negate());
    Trace("sygus-qep-debug") << "getQe on " << qeconj << std::endl;
    // compute quantifier elimination
    std::unique_ptr<SmtEngine> smt_qe;
    initializeSubsolver(smt_qe);
    Node qeRes = smt_qe->getQuantifierElimination(qeconj, true, false);
    Trace("sygus-qep-debug") << "getQe result: " << qeRes << std::endl;
    // create single invocation conjecture, if QE was successful
    if (!expr::hasBoundVar(qeRes))
    {
      // revert skolems
      qeRes = xmaxfk.rapply(qeRes);
      // add back the uneliminated variables
      if (!xargs.empty())
      {
        qeRes = nm->mkNode(EXISTS, nm->mkNode(BOUND_VAR_LIST, xargs), qeRes);
      }
      // remake conjecture with same solved functions
      Node newConj = mkSygusConjecture(allf, qeRes, solvedf);
      Trace("sygus-qep") << "...eliminate variables return " << newConj
                         << std::endl;
      Assert(!expr::hasFreeVar(newConj));
      return newConj;
    }
    return Node::null();
  }

  // ===== B: otherwise, eliminate functions if there are remainder functions
  if (!remf.empty())
  {
    // create new smt engine to do sygus
    std::unique_ptr<SmtEngine> smt_sy;
    initializeSubsolver(smt_sy);

    // functions-to-synthesize, keep the same formal argument list
    for (const Node& f : maxf)
    {
      std::vector<Node> formals;
      getSygusArgumentListForSynthFun(f, formals);
      smt_sy->declareSynthFun(f, false, formals);
    }
    for (const Node& v : uvars)
    {
      smt_sy->declareSygusVar(v);
    }
    // make remaining functions into skolems
    Subs xfk;
    std::map<Node, Node>::iterator itf;
    for (const Node& x : xf.d_vars)
    {
      itf = xffs.find(x);
      if (itf != xffs.end())
      {
        // will substitute function invocation by fresh skolem
        xfk.add(itf->second);
      }
    }
    Trace("sygus-qep-debug") << "skolemize based on " << xfk << std::endl;
    // body for sygus
    Node syBody = xfk.apply(qfBody);
    // miniscope to remove irrelevant conjuncts
    std::vector<Node> syConstraints;
    if (syBody.getKind() == AND)
    {
      for (const Node& sybc : syBody)
      {
        // only matter if it contains functions-to-synthesize
        if (expr::hasSubterm(sybc, maxf))
        {
          syConstraints.push_back(sybc);
        }
      }
    }
    else
    {
      syConstraints.push_back(syBody);
    }

    // assert the sygus constraints
    for (const Node& syc : syConstraints)
    {
      Trace("sygus-qep-debug") << "- constraint " << syc << std::endl;
      smt_sy->assertSygusConstraint(syc);
    }

    Result r = smt_sy->checkSynth();
    Trace("sygus-qep-debug") << "checkSynth result: " << r << std::endl;
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
      // convert si vars to formal arguments
      for (size_t i = 0, nvars = solSubs.d_vars.size(); i < nvars; i++)
      {
        std::vector<Node> fargs;
        getSygusArgumentListForSynthFun(solSubs.d_vars[i], fargs);
        Subs siToFormal;
        siToFormal.add(uvars, fargs);
        solSubs.d_subs[i] = siToFormal.apply(solSubs.d_subs[i]);
        Assert(!expr::hasFreeVar(solSubs.d_subs[i]));
      }
      // extended functions have a definition in terms of the originals
      xf.applyToRange(solSubs, true);
      Trace("sygus-qep-debug")
          << "...after revert extensions : " << solSubs << std::endl;
      Trace("sygus-qep-debug")
          << "Previous solution set : " << solvedf << std::endl;
      // solSubs are correct, now update previous solutions
      solSubs.applyToRange(solvedf, true);
      // now append new solutions to solved
      solvedf.append(solSubs);
      Trace("sygus-qep-debug") << "...updated to : " << solvedf << std::endl;

      // get the original conjecture and update it with the new solutions
      Node bodyNorm = xf.apply(qfBody, true);
      Node sbvl = nm->mkNode(BOUND_VAR_LIST, uvars);
      Node conj = nm->mkNode(EXISTS, sbvl, bodyNorm.negate());
      Trace("sygus-qep-debug2")
          << "...conjecture reverted to : " << conj << std::endl;
      conj = solSubs.apply(conj);
      Trace("sygus-qep-debug2")
          << "...after current solutions : " << conj << std::endl;

      // reconstruct the new conjecture
      Node fsRes = mkSygusConjecture(allf, conj, solvedf);
      Trace("sygus-qep") << "...eliminate functions return " << fsRes
                         << std::endl;
      return fsRes;
    }
  }
  Trace("sygus-qep") << "...will solve using standard si" << std::endl;
  return Node::null();
}

bool SygusQePreproc::getMaximalArityFuncs(const std::vector<Node>& unsf,
                                          std::vector<Node>& maxf)
{
  Assert(!unsf.empty());
  size_t maxArity = 0;
  TypeNode maxType;
  bool maxArityValid = true;
  for (const Node& f : unsf)
  {
    TypeNode tn = f.getType();
    size_t arity = tn.isFunction() ? tn.getNumChildren() - 1 : 0;
    Trace("sygus-qep-debug2")
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
  for (const Node& f : unsf)
  {
    TypeNode tn = f.getType();
    if (tn == maxType)
    {
      maxf.push_back(f);
    }
  }
  return true;
}

bool SygusQePreproc::getRemainingFunctions(
    const std::vector<Node>& unsf,
    const std::vector<Node>& maxf,
    Subs& remf,
    Subs& xf,
    const std::vector<Node>& xargs,
    const std::map<Node, std::vector<Node>>& rargs)
{
  std::map<Node, std::vector<Node>>::const_iterator itr;
  // deompose into maximal arity functions and remaining functions
  for (const Node& f : unsf)
  {
    if (std::find(maxf.begin(), maxf.end(), f) != maxf.end())
    {
      // already included in maxf, don't add to remf
      continue;
    }
    itr = rargs.find(f);
    if (itr == rargs.end())
    {
      // does not occur in conjecture, no change needed
      remf.add(f, f);
      xf.add(f, f);
      continue;
    }
    // extend it to the extended function app, based on the arguments that f
    // is applied to
    if (!extendFuncArgs(f, remf, xf, xargs, itr->second))
    {
      return false;
    }
  }
  return true;
}

bool SygusQePreproc::extendFuncArgs(Node f,
                                    Subs& remf,
                                    Subs& xf,
                                    const std::vector<Node>& xargs,
                                    const std::vector<Node>& fargs)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("sygus-qep-ext") << f << " was applied to " << fargs << ", required "
                         << xargs << std::endl;
  Assert(!xargs.empty());
  Assert(fargs.size() <= xargs.size());

  // argument type of xargs -> range type of f
  std::vector<TypeNode> xats;
  for (const Node& xa : xargs)
  {
    xats.push_back(xa.getType());
  }
  // make the extended function
  TypeNode rangeT = f.getType();
  if (rangeT.isFunction())
  {
    rangeT = rangeT.getRangeType();
    if (fargs.empty())
    {
      Trace("sygus-qep-ext")
          << "...did not have single invocation" << std::endl;
      return false;
    }
  }
  TypeNode newT = nm->mkFunctionType(xats, rangeT);
  Node newF = nm->mkSkolem("xf", newT);
  Trace("sygus-qep-ext") << "Made function " << newF << " of type " << newT
                         << std::endl;

  std::vector<Node> fv;
  // start with the extended arguments
  std::vector<Node> fa = xargs;
  for (const Node& v : fargs)
  {
    fv.push_back(nm->mkBoundVar(v.getType()));
  }
  std::vector<Node> xv;
  // start with the function arguments
  std::vector<Node> xa = fargs;
  for (const Node& v : xargs)
  {
    xv.push_back(nm->mkBoundVar(v.getType()));
  }
  // now map
  std::vector<Node>::const_iterator ita;
  for (size_t i = 0, nargs = fargs.size(); i < nargs; i++)
  {
    ita = std::find(xargs.begin(), xargs.end(), fargs[i]);
    if (ita == xargs.end())
    {
      Trace("sygus-qep-ext") << "...could not find " << fargs[i] << std::endl;
      return false;
    }
    // connect the transformation
    size_t index = std::distance(xargs.begin(), ita);
    fa[index] = fv[i];
    xa[i] = xv[index];
  }
  Trace("sygus-qep-ext") << "fv/fa: " << fv << " " << fa << std::endl;
  Trace("sygus-qep-ext") << "xv/xa: " << xv << " " << xa << std::endl;
  // Add the pair
  //   f, (lambda ((x domainTs)) (newF x xargs2))
  // to remf, where the latter term has the same type as f.
  Node flam = mkLambdaApp(fv, newF, fa);
  remf.add(f, flam);
  Trace("sygus-qep-ext") << "extendFuncArgs: Extend: " << f << " -> " << flam
                         << std::endl;
  // also make the reverse mapping
  //   newF, (lambda (xargs1 xargs2) (f xargs1))
  // to xf, where the latter term has the same type as newF.
  Node xlam = mkLambdaApp(xv, f, xa);
  xf.add(newF, xlam);
  Trace("sygus-qep-ext") << "extendFuncArgs: Restrict: " << newF << " -> "
                         << xlam << std::endl;
  return true;
}

Node SygusQePreproc::mkLambdaApp(const std::vector<Node>& vars,
                                 Node f,
                                 const std::vector<Node>& args)
{
  NodeManager* nm = NodeManager::currentNM();
  Node ret = f;
  if (!args.empty())
  {
    std::vector<Node> aargs;
    aargs.push_back(f);
    aargs.insert(aargs.end(), args.begin(), args.end());
    ret = nm->mkNode(APPLY_UF, aargs);
  }
  if (!vars.empty())
  {
    Node bvl = nm->mkNode(BOUND_VAR_LIST, vars);
    ret = nm->mkNode(LAMBDA, bvl, ret);
  }
  return ret;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
