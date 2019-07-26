/*********************                                                        */
/*! \file proof_db_sc.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof side conditions
 **/

#include "theory/proof_db_sc.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

ProofDbScEval::ProofDbScEval()
{
  d_symTable[std::string("flatten")] = sc_flatten;
  d_symTable[std::string("re_loop_elim")] = sc_re_loop_elim;
}

void ProofDbScEval::registerSideCondition(Node sc)
{
  if (sc.getKind() == EQUAL)
  {
    buildOperatorTable(sc[0]);
  }
}

void ProofDbScEval::buildOperatorTable(Node n)
{
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      // if it is APPLY_UF, we check if it is a side condition
      if (cur.getKind() == APPLY_UF)
      {
        Node op = cur.getOperator();
        std::map<Node, SideConditionId>::iterator ito = d_opTable.find(op);
        // if not already processed
        if (ito == d_opTable.end())
        {
          std::stringstream ss;
          ss << op;
          Trace("proof-db-sc-init") << "Initialize side condition symbol "
                                    << ss.str() << "..." << std::endl;
          std::map<std::string, SideConditionId>::iterator it =
              d_symTable.find(ss.str());
          if (it != d_symTable.end())
          {
            Trace("proof-db-sc-init")
                << "*** Associate " << op << " / " << it->second << std::endl;
            d_opTable[op] = it->second;
          }
          else
          {
            Warning() << "Could not find side condition for operator " << op
                      << std::endl;
            AlwaysAssert(false);
          }
        }
      }
      // can be nested
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());
}

Node ProofDbScEval::evaluate(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.push_back(cur);
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (cur.getKind() == APPLY_UF)
      {
        ret = evaluateApp(cur.getOperator(), children);
        if (ret.isNull())
        {
          // failed side condition
          return ret;
        }
      }
      else if (childChanged)
      {
        if (cur.getMetaKind() == metakind::PARAMETERIZED)
        {
          children.insert(children.begin(), cur.getOperator());
        }
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node ProofDbScEval::evaluateApp(Node op, const std::vector<Node>& args)
{
  std::map<Node, SideConditionId>::iterator it = d_opTable.find(op);
  if (it == d_opTable.end())
  {
    Warning() << "Could not find side condition for operator " << op
              << " during evaluation" << std::endl;
    AlwaysAssert(false);
    return Node::null();
  }
  // ----------------------------- specific lookup into side conditions
  Trace("proof-db-sc") << "Run side condition " << it->second << " with args "
                       << args << std::endl;
  Node ret;
  if (it->second == sc_flatten)
  {
    Assert(args.size() == 1);
    ret = flatten(args[0]);
  }
  else if (it->second == sc_re_loop_elim)
  {
    Assert(args.size() == 1);
    ret = reLoopElim(args[0]);
  }
  else
  {
    Warning() << "Unknown side condition id " << it->second << " for operator "
            << op << std::endl;
  }
  Trace("proof-db-sc") << "Side condition returned " << ret << std::endl;
  return ret;
}

bool ProofDbScEval::isSideConditionOp(Node op) const
{
  return d_opTable.find(op) != d_opTable.end();
}

////// side conditions

Node flattenCollect( Kind k, Node n, Node acc )
{
  if( n.getKind()==k )
  {
    Node ret = flattenCollect(k,n[1],acc);
    return flattenCollect(k,n[0],ret);
  }
  else if( acc.isNull() )
  {
    return n;
  }
  else
  {
    return NodeManager::currentNM()->mkNode(k,n,acc);
  }
}
Node ProofDbScEval::flatten(Node n)
{
  Assert(n.getNumChildren() == 2);
  Node acc;
  return flattenCollect(n.getKind(),n,acc);
}

Node ProofDbScEval::reLoopElim(Node n)
{
  return n;
}

}  // namespace theory
}  // namespace CVC4
