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

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool isSingleInvocationType(const std::vector<Node>& fs)
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

bool isSingleInvocation(const std::vector<Node>& fs,
                        Node conj,
                        std::map<Node, Node>& ffs,
                        std::vector<Node>& args)
{
  if (fs.empty())
  {
    return true;
  }
  Assert(isSingleInvocationType(fs));
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
              // not applied to bound variable
              if (cur[i].getKind() != BOUND_VARIABLE)
              {
                return false;
              }
              args.push_back(cur[i]);
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

bool isSingleInvocation(const std::vector<Node>& fs,
                        Node conj,
                        std::vector<Node>& args)
{
  std::map<Node, Node> ffs;
  return isSingleInvocation(fs, conj, ffs, args);
}

void getSingleInvocations(const std::vector<Node>& fs,
                        Node conj,
                        std::map<Node, std::vector<Node>>& args)
{
  if (fs.empty())
  {
    return;
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
                  ita->second.clear();
                  break;
                }
              }
              else
              {
                // not applied to bound variable
                if (cur[i].getKind() != BOUND_VARIABLE)
                {
                  args[op].clear();
                  break;
                }
                args[op].push_back(cur[i]);
              }
            }
          }
        }
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
