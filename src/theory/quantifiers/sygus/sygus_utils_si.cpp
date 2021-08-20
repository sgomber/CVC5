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
#include "theory/quantifiers/sygus/sygus_utils.h"

using namespace cvc5::kind;

namespace cvc5 {
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
  if (!areSameType(fs))
  {
    Trace("sygus-si-infer-debug") << "...si failed due to type" << std::endl;
    return false;
  }
  bool argsSet = false;
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
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
          Trace("sygus-si-infer-debug")
              << "...si failed due to higher-order " << cur << std::endl;
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
                Trace("sygus-si-infer-debug")
                    << "...si failed due to different arguments " << cur
                    << std::endl;
                return false;
              }
            }
            else
            {
              // take into account requirements of unique bound variable
              if (!addUniqueBoundVar(reqBoundVar, cur[i], args))
              {
                Trace("sygus-si-infer-debug")
                    << "...si failed due to base " << cur << std::endl;
                return false;
              }
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
                                      bool reqBoundVar)
{
  std::map<Node, Node> ffs;
  std::vector<Node> args;
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
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
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

bool SygusSiUtils::getMaximalArityFunctions(
    const std::map<Node, std::vector<Node>>& args,
    std::vector<Node>& maxf,
    std::vector<Node>& maxArgs)
{
  if (args.empty())
  {
    return true;
  }
  size_t maxArity = 0;
  for (const std::pair<const Node, std::vector<Node>>& as : args)
  {
    if (maxf.empty() || as.second.size() > maxArity)
    {
      maxf.clear();
      maxArity = as.second.size();
    }
    if (as.second.size() == maxArity)
    {
      maxf.push_back(as.first);
    }
  }
  Assert(!maxf.empty());
  std::map<Node, std::vector<Node>>::const_iterator it = args.find(maxf[0]);
  Assert(it != args.end());
  // take the first maximal arity function's arguments as reference
  maxArgs.insert(maxArgs.end(), it->second.begin(), it->second.end());
  // ensure that all invocations are a subset
  for (const std::pair<const Node, std::vector<Node>>& as : args)
  {
    for (const Node& a : as.second)
    {
      if (std::find(maxArgs.begin(), maxArgs.end(), a) == maxArgs.end())
      {
        // argument does not fit what a maximal arity function was applied to
        return false;
      }
    }
  }
  return true;
}

void SygusSiUtils::partitionConjecture(const std::vector<Node>& fs,
                                       Node conj,
                                       Node& cc,
                                       Node& nc)
{
  std::vector<Node> c;
  SygusUtils::decomposeAnd(conj, c);
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

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
