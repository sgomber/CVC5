/*********************                                                        */
/*! \file sygus_utils_si.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus utilities for single invocation
 **/

#include "theory/quantifiers/sygus/sygus_utils_si.h"

#include "expr/node_algorithm.h"
#include "theory/quantifiers/single_inv_partition.h"
#include "theory/quantifiers/sygus/sygus_utils.h"
#include "theory/smt_engine_subsolver.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool SygusSiUtils::areSameType(const std::vector<Node>& fs)
{
  Assert(!fs.empty());
  // just make free variables, assuming that all functions have same type
  TypeNode tn = fs[0].getType();
  for (size_t i = 1, nfs = fs.size(); i < nfs; i++)
  {
    if (fs[i].getType() != tn)
    {
      return false;
    }
  }
  return true;
}

bool addUniqueBoundVar(bool reqBoundVar, Node v, std::vector<Node>& args)
{
  if (!reqBoundVar)
  {
    args.push_back(v);
    return true;
  }
  else if (v.getKind() != BOUND_VARIABLE
           || std::find(args.begin(), args.end(), v) != args.end())
  {
    return false;
  }
  args.push_back(v);
  return true;
}

bool SygusSiUtils::isSingleInvocation(const std::vector<Node>& fs,
                                      Node conj,
                                      std::map<Node, Node>& ffs,
                                      std::vector<Node>& args,
                                      bool reqBoundVar)
{
  if (fs.empty())
  {
    return true;
  }
  Assert(areSameType(fs));
  bool argsSet = false;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::unordered_set<TNode, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(conj);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited.insert(cur);
      // if it is a function-to-synthesize
      if (std::find(fs.begin(), fs.end(), cur) != fs.end())
      {
        if (cur.getType().isFunction())
        {
          // higher-order instance, always fail
          return false;
        }
        // corner case of constant function-to-synthesize
        ffs[cur] = cur;
      }
      else if (cur.getKind() == APPLY_UF)
      {
        Node op = cur.getOperator();
        // if it is a function we care about
        if (std::find(fs.begin(), fs.end(), op) != fs.end())
        {
          Assert(!argsSet || cur.getNumChildren() == args.size());
          for (size_t i = 0, nchild = cur.getNumChildren(); i < nchild; i++)
          {
            if (argsSet)
            {
              if (cur[i] != args[i])
              {
                // different arguments
                return false;
              }
            }
            else
            {
              // take into account requirements of unique bound variable
              addUniqueBoundVar(reqBoundVar, cur[i], args);
            }
          }
          // update the map
          if (ffs.find(op) == ffs.end())
          {
            ffs[op] = cur;
          }
          argsSet = true;
          continue;
        }
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  // add dummy arguments in the corner case that no functions appeared
  if (!argsSet)
  {
    TypeNode ft = fs[0].getType();
    if (ft.isFunction())
    {
      NodeManager* nm = NodeManager::currentNM();
      std::vector<TypeNode> argTypes = ft.getArgTypes();
      for (const TypeNode& at : argTypes)
      {
        args.push_back(nm->mkBoundVar(at));
      }
    }
  }
  return true;
}

bool SygusSiUtils::isSingleInvocation(const std::vector<Node>& fs,
                                      Node conj,
                                      std::vector<Node>& args,
                                      bool reqBoundVar)
{
  std::map<Node, Node> ffs;
  return isSingleInvocation(fs, conj, ffs, args, reqBoundVar);
}

bool SygusSiUtils::getSingleInvocations(const std::vector<Node>& fs,
                                        Node conj,
                                        std::map<Node, std::vector<Node>>& args,
                                        bool reqBoundVar,
                                        bool reqAllValid)
{
  if (fs.empty())
  {
    return true;
  }
  std::map<Node, std::vector<Node>>::iterator ita;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::unordered_set<TNode, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(conj);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited.insert(cur);
      // if it is a function-to-synthesize
      if (std::find(fs.begin(), fs.end(), cur) != fs.end())
      {
        // corner case of constant function-to-synthesize or higher-order
        // instance, clear to ensure empty range
        if (reqAllValid && cur.getType().isFunction())
        {
          Trace("sygus-si-infer-debug")
              << "...get sii failed due to higher-order " << cur << std::endl;
          return false;
        }
        args[cur].clear();
      }
      else if (cur.getKind() == APPLY_UF)
      {
        Node op = cur.getOperator();
        // if it is a function we care about
        if (std::find(fs.begin(), fs.end(), op) != fs.end())
        {
          ita = args.find(op);
          // have we set its arguments?
          bool argsSet = ita != args.end();
          // are its arguments still valid (non-empty)?
          if (!argsSet || !ita->second.empty())
          {
            Assert(!argsSet || cur.getNumChildren() == ita->second.size());
            for (size_t i = 0, nchild = cur.getNumChildren(); i < nchild; i++)
            {
              if (argsSet)
              {
                if (cur[i] != ita->second[i])
                {
                  // different arguments
                  if (reqAllValid)
                  {
                    Trace("sygus-si-infer-debug")
                        << "...get sii failed due to different invocation "
                        << cur << std::endl;
                    return false;
                  }
                  ita->second.clear();
                  break;
                }
              }
              else
              {
                // check applied to unique bound variable
                if (!addUniqueBoundVar(reqBoundVar, cur[i], args[op]))
                {
                  if (reqAllValid)
                  {
                    Trace("sygus-si-infer-debug")
                        << "...get sii failed due to base " << cur << std::endl;
                    return false;
                  }
                  args[op].clear();
                  break;
                }
              }
            }
          }
        }
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  return true;
}

void decomposeAnd(Node conj, std::vector<Node>& c)
{
  if (conj.getKind() == AND)
  {
    // nested?
    c.insert(c.end(), conj.begin(), conj.end());
  }
  else
  {
    c.push_back(conj);
  }
}

void SygusSiUtils::partitionConjecture(const std::vector<Node>& fs,
                                       Node conj,
                                       Node& cc,
                                       Node& nc)
{
  std::vector<Node> c;
  decomposeAnd(conj, c);
  std::vector<Node> ccc;
  std::vector<Node> ncc;
  for (const Node& conjc : c)
  {
    // determine if the conjunction contains fs
    if (expr::hasSubterm(conjc, fs))
    {
      ccc.push_back(conjc);
    }
    else
    {
      ncc.push_back(conjc);
    }
  }
  NodeManager* nm = NodeManager::currentNM();
  cc = nm->mkAnd(ccc);
  nc = nm->mkAnd(ncc);
}

Node SygusSiUtils::coerceSingleInvocation(
    const std::vector<Node>& fs,
    Node conj,
    std::map<Node, std::vector<Node>>& args)
{
  Trace("sygus-si-infer") << "coerceSingleInvocation " << fs << " on " << conj
                          << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  TypeNode intTn = nm->integerType();

  // Construct an SMT problem corresponding to whether we can make the problem
  // be single invocation.
  // Formal argument list for each function
  std::map<Node, std::map<TypeNode, std::vector<Node>>> ftypevars;
  std::map<Node, std::vector<Node>> fvars;
  // Mapping conjunctions, arguments to a term that the function is invoked
  TypeNode htn = nm->mkFunctionType({intTn, intTn, intTn}, intTn);
  Node h = nm->mkSkolem("h", htn);
  // all terms
  std::vector<Node> gs;
  std::map<Node, size_t> gsId;
  // ids per type
  std::map<TypeNode, size_t> typeId;
  // the assertions
  std::vector<Node> asserts;

  // compute the maximum type arities
  std::map<TypeNode, size_t> maxTypeArgs;
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
      }
      Node ka = nm->mkSkolem("a", intTn);
      ftvs[fa].push_back(ka);
      fvs.push_back(ka);
    }
    for (const std::pair<const TypeNode, std::vector<Node>>& fa : ftvs)
    {
      if (fa.second.size() > maxTypeArgs[fa.first])
      {
        maxTypeArgs[fa.first] = fa.second.size();
      }
      if (fa.second.size() > 1)
      {
        Node fadistinct = nm->mkNode(DISTINCT, fa.second);
        // ASSERT: distinct( a1 ... an ) for a1 ... an of same type T
        asserts.push_back(fadistinct);
      }
    }
  }
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
  Node origConj = SygusUtils::decomposeConjectureBody(conj, vars);
  std::vector<Node> oconj;
  decomposeAnd(origConj, oconj);

  // for each conjunction
  std::map<size_t, std::map<Node, std::vector<Node>>> gArgs;
  for (size_t i = 0, nconj = oconj.size(); i < nconj; i++)
  {
    Node c = oconj[i];
    Node cid = nm->mkConst(Rational(i));
    // get the single invocations for each function
    std::map<Node, std::vector<Node>>& gas = gArgs[i];
    if (!getSingleInvocations(fs, c, gas, false, true))
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
        }
        Node gid = nm->mkConst(Rational(gsId[g]));
        TypeNode fvtn = fvs[j].getType();
        Assert(typeId.find(fvtn) != typeId.end());
        Node tid = nm->mkConst(Rational(typeId[fvtn]));
        Node happ = nm->mkNode(APPLY_UF, h, cid, tid, fvs[j]);
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
  std::unordered_set<Node, NodeHashFunction> allSiVars;
  for (const std::pair<const TypeNode, size_t> mt : maxTypeArgs)
  {
    for (size_t i = 0; i < mt.second; i++)
    {
      std::stringstream ss;
      ss << "s_" << i << "_" << mt.first;
      Node s = nm->mkBoundVar(ss.str(), mt.first);
      siVars[mt.first].push_back(s);
      allSiVars.insert(s);
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
      std::vector<Node>& svars = siVars[v.getType()];
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
            && allSiVars.find(eqs[1]) == allSiVars.end())
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

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
