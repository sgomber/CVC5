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
#include "theory/quantifiers/sygus/si_infer.h"
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
  SygusUtils::decomposeSygusConjecture(q, allf, unsf, solvedf);
  if (unsf.empty())
  {
    // probably should never happen
    Trace("sygus-qep") << "...fully solved, success." << std::endl;
    return Node::null();
  }
  Trace("sygus-qep-debug") << "- functions = " << allf << std::endl;
  Trace("sygus-qep-debug") << "- init unsolved = " << unsf << std::endl;
  Trace("sygus-qep-debug") << "- init solved = " << solvedf << std::endl;

  Trace("sygus-qep") << "Coerce single invocation..." << std::endl;
  // Otherwise, we coerce into "typed single invocation form", where
  // all functions are applied to a subset of arguments targetArgs, where maxf
  // is a non-empty set of allf that are applied to all arguments in targetArgs
  // (in any order).
  std::vector<Node> maxf;
  std::vector<Node> targetArgs;
  std::map<Node, std::vector<Node>> rargs;
  Node siBody = SingleInvocationInference::coerceSingleInvocation(
      unsf, q[1], maxf, targetArgs, rargs);
  if (siBody.isNull())
  {
    Trace("sygus-qep") << "...failed to coerce to single invocation"
                       << std::endl;
    return Node::null();
  }
  Trace("sygus-qep-debug") << "...single invocation with target args = "
                           << targetArgs << std::endl;
  Trace("sygus-qep-debug") << "...max functions = " << maxf << std::endl;
  if (maxf.empty())
  {
    Trace("sygus-qep") << "...trivial (no functions to synthesize)"
                       << std::endl;
    return Node::null();
  }
  // Get the function transformation. We also compute methods for extending
  // them to extended functions in xf. The substitutions remf converts the
  // remaining functions to extended ones (each whose argument types match
  // targetArgs), and the map xf converts the extended functions back to the
  // originals.
  Subs remf;
  Subs xf;
  std::map<Node, Node> xmap;
  Node xbody = siBody;
  if (!getFunctionTransforms(unsf, remf, xf, xmap, targetArgs, rargs))
  {
    // arity mismatch for functions, we are done
    Trace("sygus-qep") << "...get function transforms, fail." << std::endl;
    AlwaysAssert(false);
    return Node::null();
  }
  std::vector<Node> xmaxf;
  for (const Node& f : maxf)
  {
    Assert(xmap.find(f) != xmap.end());
    xmaxf.push_back(xmap[f]);
  }
  Trace("sygus-qep-debug") << "- remaining-to-extension = " << remf
                           << std::endl;
  Trace("sygus-qep-debug") << "- extension-to-remaining = " << xf << std::endl;
  Trace("sygus-qep-debug") << "- extended max functions = " << xmaxf
                           << std::endl;
  // decompose the body of the synthesis conjecture
  std::vector<Node> uvars;
  Node qfBody = SygusUtils::decomposeConjectureBody(xbody, uvars);

  // lift remaining functions to extended functions
  // we rewrite the body of the conjecture only, to preserve single invocation
  qfBody = remf.apply(qfBody, true);
  Trace("sygus-qep-debug") << "Extended and normalized body:" << qfBody
                           << std::endl;

  // Check single invocation with respect to the extension.
  std::map<Node, Node> xffs;
  std::vector<Node> xtargetArgs;
  Trace("sygus-qep-debug")
      << "Check single invocation with respect to all extended functions "
      << xf.d_vars << ": " << qfBody << std::endl;
  if (!SygusSiUtils::isSingleInvocation(xf.d_vars, qfBody, xffs, xtargetArgs))
  {
    Trace("sygus-qep") << "...not single invocation after extension"
                       << std::endl;
    AlwaysAssert(false);
    // not single invocation
    return Node::null();
  }
  Assert(targetArgs.size() == xtargetArgs.size());
  Trace("sygus-qep-debug") << "...extended single invocation with args = "
                           << xtargetArgs << std::endl;

  NodeManager* nm = NodeManager::currentNM();

  // ===== A: if there free variables apart from args, do quantifier elimination
  if (uvars.size() > xtargetArgs.size())
  {
    Subs xmaxfk;
    xmaxfk.add(xtargetArgs);
    std::vector<Node> qevars;
    for (const Node& v : xbody[0][0])
    {
      if (std::find(xtargetArgs.begin(), xtargetArgs.end(), v)
          == xtargetArgs.end())
      {
        qevars.push_back(v);
      }
    }
    Assert(!qevars.empty());
    std::map<Node, Node>::iterator itf;
    for (const Node& x : xf.d_vars)
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
      if (!xtargetArgs.empty())
      {
        qeRes =
            nm->mkNode(EXISTS, nm->mkNode(BOUND_VAR_LIST, xtargetArgs), qeRes);
      }
      // convert back to original functions
      qeRes = xf.apply(qeRes);

      // remake conjecture with same solved functions
      Node newConj = SygusUtils::mkSygusConjecture(allf, qeRes, solvedf);
      Trace("sygus-qep") << "...eliminate variables return " << newConj
                         << std::endl;
      AlwaysAssert(!expr::hasFreeVar(newConj));
      return newConj;
    }
    return Node::null();
  }

  // if we don't require reordering or dropping arguments, we can just solve
  // with the standard single invocation solver
  if (maxf.size() == unsf.size())
  {
    bool reqArgReorder = false;
    for (const std::pair<Node, std::vector<Node>>& r : rargs)
    {
      Assert(r.second.size() == targetArgs.size());
      for (size_t i = 0, ntargetArgs = targetArgs.size(); i < ntargetArgs; i++)
      {
        if (r.second[i] != targetArgs[i])
        {
          reqArgReorder = true;
          break;
        }
      }
      if (reqArgReorder)
      {
        break;
      }
    }
    if (!reqArgReorder)
    {
      Trace("sygus-qep")
          << "...no argument reordering, we can solve with single invocation."
          << std::endl;
      return Node::null();
    }
  }

  // ===== B: otherwise, eliminate functions if there are remainder functions

  // functions-to-synthesize, keep the same formal argument list
  Assert(!maxf.empty());
  Assert(xmaxf.size() == maxf.size());
  std::map<Node, std::vector<Node>> formals;
  std::map<Node, std::vector<Node>> xformals;
  for (size_t i = 0, nmaxf = maxf.size(); i < nmaxf; i++)
  {
    Node fn = maxf[i];
    Node xfn = xmaxf[i];
    Trace("sygus-qep-debug") << "Compute formal argument list for " << xfn
                             << " from " << fn << std::endl;
    // formal argument list is permuted based on the transformation
    SygusUtils::getSygusArgumentListForSynthFun(fn, formals[fn]);
    Trace("sygus-qep-debug") << "...original :  " << formals[fn] << std::endl;
    xformals[xfn].clear();
    if (!formals[fn].empty())
    {
      std::vector<Node> faargs;
      faargs.push_back(fn);
      faargs.insert(faargs.end(), formals[fn].begin(), formals[fn].end());
      Node fapp = nm->mkNode(APPLY_UF, faargs);
      Trace("sygus-qep-debug") << "  based on " << fapp << std::endl;
      Node xfapp = remf.apply(fapp, true);
      Trace("sygus-qep-debug") << "  transformed to " << xfapp << std::endl;
      xformals[xfn].insert(xformals[xfn].end(), xfapp.begin(), xfapp.end());
    }
    Trace("sygus-qep-debug")
        << "...transformed :  " << xformals[xfn] << std::endl;
  }

  // create new smt engine to do sygus
  std::unique_ptr<SmtEngine> smt_sy;
  initializeSubsolver(smt_sy);

  for (const Node& xfn : xmaxf)
  {
    Assert(xformals.find(xfn) != xformals.end());
    Trace("sygus-qep-debug") << "- synth fun " << xfn << std::endl;
    smt_sy->declareSynthFun(xfn, false, xformals[xfn]);
  }
  for (const Node& v : uvars)
  {
    Trace("sygus-qep-debug") << "- sygus var " << v << std::endl;
    smt_sy->declareSygusVar(v);
  }
  // make remaining functions into skolems
  Subs xfk;
  std::map<Node, Node>::iterator itf;
  for (const Node& x : xf.d_vars)
  {
    if (std::find(xmaxf.begin(), xmaxf.end(), x) != xmaxf.end())
    {
      continue;
    }
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
  // Node syc;
  // Node syn;
  // TODO: use partition method?
  // miniscope to remove irrelevant conjuncts
  std::vector<Node> syConstraints;
  if (syBody.getKind() == AND)
  {
    for (const Node& sybc : syBody)
    {
      // only matter if it contains functions-to-synthesize
      if (expr::hasSubterm(sybc, xmaxf))
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
  Trace("sygus-qep") << "checkSynth to eliminate functions" << std::endl;
  Result r = smt_sy->checkSynth();
  Trace("sygus-qep") << "checkSynth result: " << r << std::endl;
  if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    std::map<Node, Node> solMap;
    smt_sy->getSynthSolutions(solMap);
    Subs solSubs;
    for (size_t i = 0, nmaxf = maxf.size(); i < nmaxf; i++)
    {
      Node fn = maxf[i];
      TNode xfn = xmaxf[i];
      Assert(solMap.find(xfn) != solMap.end());
      TNode xsol = solMap[xfn];
      Trace("sygus-qep-debug")
          << "Solution initial : " << xfn << " -> " << xsol << std::endl;
      // transform the solution
      Node fsol = remf.apply(fn);
      fsol = fsol.substitute(xfn, xsol);
      // apply to original formal arguments
      fsol = mkLambdaApp(formals[fn], fsol, formals[fn]);
      fsol = Rewriter::rewrite(fsol);
      Trace("sygus-qep-debug")
          << "Converted to : " << fn << " -> " << fsol << std::endl;

      Trace("sygus-qep-debug")
          << "...xtargetArgs = " << xtargetArgs << std::endl;
      Trace("sygus-qep-debug")
          << "...xformals[" << xfn << "] = " << xformals[xfn] << std::endl;
      Subs siToFormal;
      siToFormal.add(xtargetArgs, xformals[xfn]);
      fsol = siToFormal.apply(fsol);
      Trace("sygus-qep-debug") << "Revert formals " << fsol << std::endl;

      solSubs.add(fn, fsol);
      Trace("sygus-qep-debug")
          << "Modified to : " << fn << " -> " << fsol << std::endl;
    }
    Trace("sygus-qep-debug") << "Solution : " << solSubs << std::endl;
    // undo the skolemization of the extended functions
    xfk.rapplyToRange(solSubs);
    Trace("sygus-qep-debug")
        << "...after unskolemize : " << solSubs << std::endl;
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
    Node sbvl = nm->mkNode(BOUND_VAR_LIST, xtargetArgs);
    Node conj = nm->mkNode(EXISTS, sbvl, bodyNorm.negate());
    Trace("sygus-qep-debug2")
        << "...conjecture reverted to : " << conj << std::endl;
    conj = solSubs.apply(conj, true);
    Trace("sygus-qep-debug2")
        << "...after current solutions : " << conj << std::endl;

    // reconstruct the new conjecture
    Node fsRes = SygusUtils::mkSygusConjecture(allf, conj, solvedf);
    Trace("sygus-qep") << "...eliminate functions return " << fsRes
                       << std::endl;
    AlwaysAssert(!expr::hasFreeVar(fsRes));
    return fsRes;
  }

  Trace("sygus-qep") << "...failed to eliminate functions" << std::endl;
  return Node::null();
}

bool SygusQePreproc::getFunctionTransforms(
    const std::vector<Node>& unsf,
    Subs& remf,
    Subs& xf,
    std::map<Node, Node>& xmap,
    const std::vector<Node>& targetArgs,
    const std::map<Node, std::vector<Node>>& rargs)
{
  std::map<Node, std::vector<Node>>::const_iterator itr;
  // get function transformation for each function in unsf
  for (const Node& f : unsf)
  {
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
    Node x = getFunctionTransform(f, remf, xf, targetArgs, itr->second);
    if (x.isNull())
    {
      return false;
    }
    xmap[f] = x;
  }
  return true;
}

Node SygusQePreproc::getFunctionTransform(Node f,
                                          Subs& remf,
                                          Subs& xf,
                                          const std::vector<Node>& targetArgs,
                                          const std::vector<Node>& fargs)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("sygus-qep-ext") << f << " was applied to " << fargs << ", required "
                         << targetArgs << std::endl;
  Assert(fargs.size() <= targetArgs.size());

  // argument type of targetArgs -> range type of f
  std::vector<TypeNode> xats;
  for (const Node& xa : targetArgs)
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
      return Node::null();
    }
  }
  TypeNode newT = xats.empty() ? rangeT : nm->mkFunctionType(xats, rangeT);
  std::stringstream ssn;
  ssn << "x" << f;
  Node newF = nm->mkBoundVar(ssn.str(), newT);
  Trace("sygus-qep-ext") << "Made function " << newF << " of type " << newT
                         << std::endl;

  std::vector<Node> fv;
  // start with the extended arguments
  std::vector<Node> fa = targetArgs;
  for (const Node& v : fargs)
  {
    fv.push_back(nm->mkBoundVar(v.getType()));
  }
  std::vector<Node> xv;
  // start with the function arguments
  std::vector<Node> xa = fargs;
  for (const Node& v : targetArgs)
  {
    xv.push_back(nm->mkBoundVar(v.getType()));
  }
  // now map
  std::vector<Node>::const_iterator ita;
  for (size_t i = 0, nargs = fargs.size(); i < nargs; i++)
  {
    ita = std::find(targetArgs.begin(), targetArgs.end(), fargs[i]);
    if (ita == targetArgs.end())
    {
      Trace("sygus-qep-ext") << "...could not find " << fargs[i] << std::endl;
      return Node::null();
    }
    // connect the transformation
    size_t index = std::distance(targetArgs.begin(), ita);
    fa[index] = fv[i];
    xa[i] = xv[index];
  }
  Trace("sygus-qep-ext") << "fv/fa: " << fv << " " << fa << std::endl;
  Trace("sygus-qep-ext") << "xv/xa: " << xv << " " << xa << std::endl;
  // Add the pair
  //   f, (lambda ((x domainTs)) (newF x targetArgs2))
  // to remf, where the latter term has the same type as f.
  Node flam = mkLambdaApp(fv, newF, fa);
  remf.add(f, flam);
  Trace("sygus-qep-ext") << "extendFuncArgs: Extend: " << f << " -> " << flam
                         << std::endl;
  // also make the reverse mapping
  //   newF, (lambda (targetArgs1 targetArgs2) (f targetArgs1))
  // to xf, where the latter term has the same type as newF.
  Node xlam = mkLambdaApp(xv, f, xa);
  xf.add(newF, xlam);
  Trace("sygus-qep-ext") << "extendFuncArgs: Restrict: " << newF << " -> "
                         << xlam << std::endl;
  return newF;
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
