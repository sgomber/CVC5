/*********************                                                        */
/*! \file arith_preprocess.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arithmetic preprocess
 **/

#include "theory/arith/arith_preprocess.h"

#include "theory/arith/arith_state.h"
#include "theory/arith/inference_manager.h"
#include "theory/skolem_lemma.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

ArithPreprocess::ArithPreprocess(ArithState& state,
                                 InferenceManager& im,
                                 ProofNodeManager* pnm,
                                 const LogicInfo& info)
    : d_im(im), d_opElim(pnm, info), d_reduced(state.getUserContext())
{
}
TrustNode ArithPreprocess::eliminate(TNode n,
                                     std::vector<SkolemLemma>& lems,
                                     bool partialOnly)
{
  return d_opElim.eliminate(n, lems, partialOnly);
}

bool ArithPreprocess::reduceAssertion(TNode atom)
{
  context::CDHashMap<Node, bool, NodeHashFunction>::const_iterator it =
      d_reduced.find(atom);
  if (it != d_reduced.end())
  {
    // already computed
    return (*it).second;
  }
  std::vector<SkolemLemma> lems;
  TrustNode tn = eliminate(atom, lems);
  for (const SkolemLemma& lem : lems)
  {
    d_im.trustedLemma(lem.d_lemma, InferenceId::ARITH_PP_ELIM_OPERATORS_LEMMA);
  }
  if (tn.isNull())
  {
    Trace("arith-pp-debug")
        << "ArithPreprocess::reduceAssertion: no reduction for " << atom
        << std::endl;
    // did not reduce
    d_reduced[atom] = false;
    return false;
  }
  Assert(tn.getKind() == TrustNodeKind::REWRITE);
  Trace("arith-pp-debug") << "ArithPreprocess::reduceAssertion: reduction for "
                          << atom << std::endl;
  Trace("arith-pp") << "ArithPreprocess::reduceAssertion: lemma "
                    << tn.getProven() << std::endl;
  // tn is of kind REWRITE, turn this into a LEMMA here
  TrustNode tlem = TrustNode::mkTrustLemma(tn.getProven(), tn.getGenerator());
  // send the trusted lemma
  d_im.trustedLemma(tlem, InferenceId::ARITH_PP_ELIM_OPERATORS);
  // mark the atom as reduced
  d_reduced[atom] = true;
  return true;
}

bool ArithPreprocess::isReduced(TNode atom) const
{
  context::CDHashMap<Node, bool, NodeHashFunction>::const_iterator it =
      d_reduced.find(atom);
  if (it == d_reduced.end())
  {
    return false;
  }
  return (*it).second;
}

TrustNode ArithPreprocess::preprocess(Node n)
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
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      TrustNode tn = eliminate(ret);
      if (!tn.isNull())
      {
        ret = tn.getNode();
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  Node ret = visited[n];
  if (ret == n)
  {
    return TrustNode::null();
  }
  return TrustNode::mkTrustRewrite(n, ret, nullptr);
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
