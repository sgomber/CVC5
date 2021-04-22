/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Single invocation inference
 */

#include "theory/quantifiers/sygus/si_infer.h"

#include <sstream>

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "theory/quantifiers/sygus/sygus_utils.h"
#include "theory/quantifiers/sygus/sygus_utils_si.h"
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {

Node SingleInvocationInference::coerceSingleInvocation(
    const std::vector<Node>& fs,
    Node conj,
    std::vector<Node>& maxf,
    std::vector<Node>& maxArgs,
    std::map<Node, std::vector<Node>>& args)
{
  Trace("sygus-si-infer") << "coerceSingleInvocation " << fs << " on " << conj
                          << std::endl;
  Assert(!fs.empty());
  /*
  Node conjs = coerceSingleInvocationSimple(fs, conj, maxf, maxArgs, args);
  if (!conjs.isNull())
  {
    return conjs;
  }
  args.clear();
  */

  NodeManager* nm = NodeManager::currentNM();
  SkolemManager * sm = nm->getSkolemManager();
  TypeNode intTn = nm->integerType();

  // Construct an SMT problem corresponding to whether we can make the problem
  // be single invocation.
  // Formal argument list for each function
  std::map<Node, std::map<TypeNode, std::vector<Node>>> ftypevars;
  std::map<Node, std::vector<Node>> fvars;
  std::map<Node, TypeNode> fvToOType;
  // Mapping conjunctions, arguments to a term that the function is invoked
  TypeNode htn = nm->mkFunctionType({intTn, intTn, intTn}, intTn);
  Node h = sm->mkDummySkolem("h", htn);
  // all terms
  std::vector<Node> gs;
  std::map<Node, size_t> gsId;
  // ids per type
  std::map<TypeNode, size_t> typeId;
  // the assertions
  std::vector<Node> asserts;

  // compute the maximum type arities
  std::map<TypeNode, size_t> maxTypeArgs;
  size_t maxTypeArity = 0;
  for (const Node& f : fs)
  {
    TypeNode ftn = f.getType();
    if (!ftn.isFunction())
    {
      continue;
    }
    std::vector<TypeNode> fas = ftn.getArgTypes();
    std::map<TypeNode, std::vector<Node>>& ftvs = ftypevars[f];
    std::vector<Node>& fvs = fvars[f];
    for (const TypeNode& fa : fas)
    {
      // ensure we have assigned this type an ID
      if (typeId.find(fa) == typeId.end())
      {
        size_t id = typeId.size();
        typeId[fa] = id;
        Trace("sygus-si-infer")
            << "  - id of type " << fa << " is " << id << std::endl;
      }
      Node ka = sm->mkDummySkolem("a", intTn);
      ftvs[fa].push_back(ka);
      fvs.push_back(ka);
      fvToOType[ka] = fa;
    }
    bool newMaxf = false;
    for (const std::pair<const TypeNode, std::vector<Node>>& fa : ftvs)
    {
      size_t prevMax = maxTypeArgs[fa.first];
      if (fa.second.size() > prevMax)
      {
        maxTypeArity += fa.second.size() - prevMax;
        maxTypeArgs[fa.first] = fa.second.size();
        maxf.clear();
        newMaxf = true;
      }
      if (fa.second.size() > 1)
      {
        Node fadistinct = nm->mkNode(DISTINCT, fa.second);
        // ASSERT: distinct( a1 ... an ) for a1 ... an of same type T
        asserts.push_back(fadistinct);
      }
    }
    if (newMaxf)
    {
      if (fas.size() < maxTypeArity)
      {
        Trace("sygus-si-infer") << "...cannot force to typed single invocation "
                                   "form due to type constraints"
                                << std::endl;
        return Node::null();
      }
      maxf.push_back(f);
    }
    else if (fas.size() == maxTypeArity)
    {
      maxf.push_back(f);
    }
  }
  Assert(!maxf.empty());
  Trace("sygus-si-infer") << "Maximum arity functions: " << maxf << std::endl;
  // all function arguments in the range of max type arguments
  Node zero = nm->mkConst(Rational(0));
  for (const Node& f : fs)
  {
    std::map<TypeNode, std::vector<Node>>& ftvs = ftypevars[f];
    for (const std::pair<const TypeNode, std::vector<Node>> ftvst : ftvs)
    {
      Assert(maxTypeArgs.find(ftvst.first) != maxTypeArgs.end());
      Node maxRange = nm->mkConst(Rational(maxTypeArgs[ftvst.first]));
      for (const Node& v : ftvst.second)
      {
        // ASSERT: 0 <= ai < |maxTypeArgs(T)|
        Node rangeConstraint = nm->mkNode(
            AND, nm->mkNode(GEQ, v, zero), nm->mkNode(LT, v, maxRange));
        asserts.push_back(rangeConstraint);
      }
    }
  }

  // decompose to conjunctions
  std::vector<Node> vars;
  Node origConj = SygusUtils::decomposeSygusBody(conj, vars);
  origConj = origConj.negate();
  std::vector<Node> oconj;
  SygusUtils::decomposeAnd(origConj, oconj);

  // for each conjunction
  std::map<size_t, std::map<Node, std::vector<Node>>> gArgs;
  for (size_t i = 0, nconj = oconj.size(); i < nconj; i++)
  {
    Node c = oconj[i];
    Node cid = nm->mkConst(Rational(i));
    // get the single invocations for each function
    std::map<Node, std::vector<Node>>& gas = gArgs[i];
    if (!SygusSiUtils::getSingleInvocations(fs, c, gas, false, true))
    {
      Trace("sygus-si-infer") << "...FAIL: conjunction " << c
                              << " is not single invocation" << std::endl;
      // conjunct by itself is not single invocation, fail
      return Node::null();
    }
    // for each function invocation
    for (const std::pair<const Node, std::vector<Node>>& ga : gas)
    {
      Node f = ga.first;
      std::vector<Node>& fvs = fvars[f];
      Assert(fvs.size() == ga.second.size());
      for (size_t j = 0, gasize = ga.second.size(); j < gasize; j++)
      {
        Node g = ga.second[j];
        if (std::find(gs.begin(), gs.end(), g) == gs.end())
        {
          gsId[g] = gs.size();
          gs.push_back(g);
          Trace("sygus-si-infer") << "  - id of ground term " << g << " is "
                                  << gsId[g] << std::endl;
        }
        Node gid = nm->mkConst(Rational(gsId[g]));
        TypeNode gtype = g.getType();
        AlwaysAssert(typeId.find(gtype) != typeId.end());
        Node tid = nm->mkConst(Rational(typeId[gtype]));
        Node happ = nm->mkNode(APPLY_UF, h, cid, tid, fvs[j]);
        Trace("sygus-si-infer")
            << "   ...make argument #" << j << " of " << f << " (ground term "
            << g << "): " << fvs[j] << " " << gtype << " is " << happ
            << " == " << gid << std::endl;
        // ASSERT: h( typeId, conjId, ai ) = gId
        asserts.push_back(happ.eqNode(gid));
      }
    }
  }

  Trace("sygus-si-infer")
      << "Query subsolver for inference of single invocation..." << std::endl;
  // now query
  std::unique_ptr<SmtEngine> siInferChecker;
  initializeSubsolver(siInferChecker);
  for (const Node& a : asserts)
  {
    Trace("sygus-si-infer") << "- assert : " << a << std::endl;
    siInferChecker->assertFormula(a);
  }
  Trace("sygus-si-infer") << "Check sat..." << std::endl;
  Result r = siInferChecker->checkSat();
  Trace("sygus-si-infer") << "...got " << r << std::endl;
  if (!r.asSatisfiabilityResult().isSat())
  {
    Trace("sygus-si-infer") << "...FAIL to solve constraints" << std::endl;
    // failed to solve constraints
    return Node::null();
  }

  // make the single invocation variables
  std::map<TypeNode, std::vector<Node>> siVars;
  for (const std::pair<const TypeNode, size_t> mt : maxTypeArgs)
  {
    for (size_t i = 0; i < mt.second; i++)
    {
      std::stringstream ss;
      ss << "s_" << i << "_" << mt.first;
      Node s = nm->mkBoundVar(ss.str(), mt.first);
      siVars[mt.first].push_back(s);
      maxArgs.push_back(s);
    }
    Trace("sygus-si-infer") << "Single invocation variables [" << mt.first
                            << "]: " << siVars[mt.first] << std::endl;
  }
  // build the single invocations for each function
  std::map<Node, Node> finvoke;
  for (const Node& f : fs)
  {
    std::vector<Node>& fvs = fvars[f];
    if (fvs.empty())
    {
      finvoke[f] = f;
      args[f].clear();
      continue;
    }
    std::vector<Node> iargs;
    std::vector<Node>& fas = args[f];
    iargs.push_back(f);
    for (const Node& v : fvs)
    {
      Node mv = siInferChecker->getValue(v);
      Assert(mv.getKind() == CONST_RATIONAL);
      Integer mvi = mv.getConst<Rational>().getNumerator();
      Assert(mvi.fitsUnsignedInt());
      uint32_t index = mvi.toUnsignedInt();
      Assert(fvToOType.find(v) != fvToOType.end());
      TypeNode vtn = fvToOType[v];
      std::vector<Node>& svars = siVars[vtn];
      Assert(index < svars.size());
      Node s = svars[index];
      iargs.push_back(s);
      fas.push_back(s);
    }
    finvoke[f] = nm->mkNode(APPLY_UF, iargs);
    Trace("sygus-si-infer")
        << "Function invocation [" << f << "]: " << finvoke[f] << std::endl;
  }
  // process each conjunction
  std::vector<Node> finalConj;
  for (size_t i = 0, nconj = oconj.size(); i < nconj; i++)
  {
    Node c = oconj[i];
    Trace("sygus-si-infer") << "Conjunct [" << i << "]: " << c << std::endl;
    Node cid = nm->mkConst(Rational(i));
    // replace single invocations
    Subs siirep;
    // for each function invocation, replace it with the original
    std::map<Node, std::vector<Node>>& gas = gArgs[i];
    std::unordered_set<Node, NodeHashFunction> sused;
    for (const std::pair<const Node, std::vector<Node>>& ga : gas)
    {
      if (ga.second.empty())
      {
        continue;
      }
      Node f = ga.first;
      std::vector<Node> fginvoke;
      fginvoke.push_back(f);
      fginvoke.insert(fginvoke.end(), ga.second.begin(), ga.second.end());
      Node fg = nm->mkNode(APPLY_UF, fginvoke);
      Assert(finvoke.find(f) != finvoke.end());
      Node fi = finvoke[f];
      Trace("sygus-si-infer")
          << "...in conjunct " << i << ", we have invocation " << fg
          << " == " << fi << std::endl;
      siirep.add(fg, fi);
      // remember the variables we used
      for (const Node& s : fi)
      {
        sused.insert(s);
      }
    }
    // replace arguments by single invocation
    Node fc = siirep.apply(c);

    // now get the assumptions
    Subs sivrep;
    std::vector<Node> assumptions;
    for (const std::pair<const TypeNode, std::vector<Node>>& siv : siVars)
    {
      Assert(typeId.find(siv.first) != typeId.end());
      Node tid = nm->mkConst(Rational(typeId[siv.first]));
      for (size_t j = 0, sivsize = siv.second.size(); j < sivsize; j++)
      {
        Node s = siv.second[j];
        if (sused.find(s) == sused.end())
        {
          // not used
          continue;
        }
        Node sivid = nm->mkConst(Rational(j));
        Node happ = nm->mkNode(APPLY_UF, h, cid, tid, sivid);
        Node mh = siInferChecker->getValue(happ);
        Assert(mh.getKind() == CONST_RATIONAL);
        Integer mhi = mh.getConst<Rational>().getNumerator();
        Assert(mhi.fitsUnsignedInt());
        uint32_t index = mhi.toUnsignedInt();
        Assert(index < gs.size());
        Node g = gs[index];
        Assert(g.getType() == siv.first);
        Trace("sygus-si-infer")
            << "...in conjunct " << i << ", we have argument " << s
            << " == " << g << std::endl;
        Node eq = s.eqNode(g);
        Node eqs = sivrep.apply(eq);
        if (eqs[1].getKind() == BOUND_VARIABLE
            && std::find(maxArgs.begin(), maxArgs.end(), eqs[1])
                   == maxArgs.end())
        {
          TNode tv = eqs[1];
          TNode ts = eqs[0];
          fc = fc.substitute(tv, ts);
          sivrep.add(eqs[1], eqs[0]);
        }
        else
        {
          assumptions.push_back(eqs.negate());
        }
      }
    }
    // apply entire substitution
    fc = sivrep.apply(fc);
    assumptions.push_back(fc);
    fc = nm->mkOr(assumptions);
    Trace("sygus-si-infer")
        << "Processed conjunct [" << i << "]: " << fc << std::endl;
    finalConj.push_back(fc);
  }

  Node fconj = nm->mkAnd(finalConj);
  // get all free variables
  std::unordered_set<Node, NodeHashFunction> ffvs;
  expr::getFreeVariables(fconj, ffvs);
  for (const Node& f : fs)
  {
    if (ffvs.find(f) != ffvs.end())
    {
      ffvs.erase(f);
    }
  }
  if (!ffvs.empty())
  {
    std::vector<Node> ffvv{ffvs.begin(), ffvs.end()};
    fconj = nm->mkNode(FORALL, nm->mkNode(BOUND_VAR_LIST, ffvv), fconj);
  }
  fconj = fconj.notNode();
  Trace("sygus-si-infer") << "Coerced conjecture: " << fconj << std::endl;
  return fconj;
}

Node SingleInvocationInference::coerceSingleInvocationSimple(
    const std::vector<Node>& fs,
    Node conj,
    std::vector<Node>& maxf,
    std::vector<Node>& maxArgs,
    std::map<Node, std::vector<Node>>& args)
{
  // maybe it is already single invocation?
  if (!SygusSiUtils::getSingleInvocations(fs, conj, args, false))
  {
    Trace("sygus-si-infer")
        << "...simple, not in weak single invocation form" << std::endl;
    return Node::null();
  }
  Trace("sygus-si-infer") << "...simple, already in weak single invocation form"
                          << std::endl;
  // single invocation, also need to ensure it is typed single invocation
  if (!SygusSiUtils::getMaximalArityFunctions(args, maxf, maxArgs))
  {
    Trace("sygus-si-infer")
        << "...simple, not in typed single invocation form" << std::endl;
    return Node::null();
  }
  Trace("sygus-si-infer")
      << "...simple, already in typed single invocation form" << std::endl;

  return conj;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
