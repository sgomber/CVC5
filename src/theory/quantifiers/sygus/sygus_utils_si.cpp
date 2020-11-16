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
  if (reqBoundVar)
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
    c.insert(c.end(), conj[0].begin(), conj[0].end());
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
  NodeManager* nm = NodeManager::currentNM();
  TypeNode intTn = nm->integerType();

  // Construct an SMT problem corresponding to whether we can make the problem
  // be single invocation.
  // Single invocation variables
  std::map<TypeNode, std::vector<Node>> siVars;
  // Formal argument list for each function
  std::map<Node, std::vector<Node>> faVars;
  // Mapping conjunctions, arguments to a term that the function is invoked
  TypeNode htn = nm->mkFunctionType({intTn, intTn}, intTn);
  Node h = nm->mkSkolem("h", htn);
  // all terms
  std::unordered_set<Node, NodeHashFunction> gs;
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
    std::map<TypeNode, size_t> farity;
    std::vector<TypeNode> fas = ftn.getArgTypes();
    for (const TypeNode& fa : fas)
    {
      farity[fa]++;
      Node ka = nm->mkSkolem("a", intTn);
      faVars[f].push_back(ka);
    }
    for (const std::pair<const TypeNode, size_t>& fa : farity)
    {
      if (fa.second > maxTypeArgs[fa.first])
      {
        maxTypeArgs[fa.first] = fa.second;
      }
    }
    if (faVars[f].size() > 1)
    {
      asserts.push_back(nm->mkNode(DISTINCT, faVars[f]));
    }
  }
  // make the single invocation variables
  for (const std::pair<const TypeNode, size_t>& mta : maxTypeArgs)
  {
    TypeNode tn = mta.first;
    for (size_t i = 0; i < mta.second; i++)
    {
      Node ks = nm->mkSkolem("s", intTn);
      siVars[tn].push_back(ks);
    }
    if (siVars[tn].size() > 1)
    {
      asserts.push_back(nm->mkNode(DISTINCT, siVars[tn]));
    }
  }
  // subset
  for (const Node& f : fs)
  {
    std::vector<Node>& fvs = faVars[f];
    for (const Node& v : fvs)
    {
      std::vector<Node>& sitvs = siVars[v.getType()];
      Assert(!sitvs.empty());
      std::vector<Node> orChildren;
      for (const Node& s : sitvs)
      {
        orChildren.push_back(v.eqNode(s));
      }
      Node orc = nm->mkOr(orChildren);
      asserts.push_back(orc);
    }
  }

  // decompose to conjunctions
  std::vector<Node> vars;
  Node origConj = SygusUtils::decomposeConjectureBody(conj, vars);
  std::vector<Node> oconj;
  decomposeAnd(origConj, oconj);
  // for each conjunction, we get the single invocations for each function
  std::map<Node, std::map<Node, std::vector<Node>>> gArgs;
  std::vector<Node> gcChildren;
  for (size_t i = 0, nconj = oconj.size(); i < nconj; i++)
  {
    Node c = oconj[i];
    Node conjid = nm->mkConst(Rational(i));
    std::map<Node, std::vector<Node>>& gas = gArgs[c];
    if (!getSingleInvocations(fs, c, gas, false, true))
    {
      return Node::null();
    }
    for (const std::pair<const Node, std::vector<Node>>& ga : gas)
    {
      std::vector<Node>& fvs = faVars[ga.first];
      Assert(fvs.size() == ga.size());
      for (size_t j = 0, gasize = ga.second.size(); j < gasize; j++)
      {
        gs.insert(ga.second[j]);
        Node happ = nm->mkNode(APPLY_UF, h, conjid, fvs[j]);
        gcChildren.push_back(happ.eqNode(ga.second[j]));
      }
    }
  }
  // conjuncts
  Node gconstraint = nm->mkAnd(gcChildren);
  asserts.push_back(gconstraint);

  // ground terms unique
  if (gs.size() > 1)
  {
    std::vector<Node> gvec{gs.begin(), gs.end()};
    Node gdistinct = nm->mkNode(DISTINCT, gvec);
    asserts.push_back(gdistinct);
  }

  return Node::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
