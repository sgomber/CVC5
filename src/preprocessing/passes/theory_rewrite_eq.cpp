/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The TheoryRewriteEq preprocessing pass.
 */

#include "preprocessing/passes/theory_rewrite_eq.h"

#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/theory_engine.h"

using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace preprocessing {
namespace passes {

TheoryRewriteEq::TheoryRewriteEq(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "theory-rewrite-eq"){};

PreprocessingPassResult TheoryRewriteEq::applyInternal(
    AssertionPipeline* assertions)
{
  // apply ppRewrite to all equalities in assertions
  for (std::size_t i = 0, size = assertions->size(); i < size; ++i)
  {
    Node assertion = (*assertions)[i];
    TrustNode trn = rewriteAssertion(assertion);
    if (!trn.isNull())
    {
      // replace based on the trust node
      assertions->replaceTrusted(i, trn);
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

TrustNode TheoryRewriteEq::rewriteAssertion(TNode n)
{
  NodeManager* nm = NodeManager::currentNM();
  TheoryEngine* te = d_preprocContext->getTheoryEngine();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
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
      if (cur.getNumChildren()==0)
      {
        visited[cur] = cur;
      }
      else if (cur.isClosure())
      {
        // do not apply within quantifiers. This is particularly important
        // for recursive function definitions, for which we do not want to
        // push the left hand side of equalities into ITE terms.
        visited[cur] = cur;
      }
      else
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
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
      if (ret.getKind() == kind::EQUAL && !ret[0].getType().isBoolean())
      {
        Trace("theory-rewrite-eq") << "TheoryRewriteEq::Rewrite: " << ret << std::endl;
        // if exactly one side is an ITE
        bool isIte0 = ret[0].getKind()==kind::ITE;
        if (isIte0 != (ret[1].getKind()==kind::ITE))
        {
          // push to children
          ret = pushIte(ret[isIte0 ? 0 : 1], ret[isIte0 ? 1 : 0]);
          TrustNode rret = rewriteAssertion(ret);
          ret = rret.isNull() ? Node(ret) : rret.getNode();
          Trace("theory-rewrite-eq") << "...push ITE to " << ret << std::endl;
        }
        else
        {
          // For example, (= x y) ---> (and (>= x y) (<= x y))
          TrustNode trn = te->ppRewriteEquality(ret);
          // can make proof producing by using proof generator from trn
          ret = trn.isNull() ? Node(ret) : trn.getNode();
        }
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
  // can make proof producing by providing a term conversion generator here
  return TrustNode::mkTrustRewrite(n, ret, nullptr);
}

Node TheoryRewriteEq::pushIte(Node ite, Node lhs)
{
  NodeManager * nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(ite);
  do {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end()) {
      visited[cur] = Node::null();
      if (cur.getKind()==ITE)
      {
        visit.push_back(cur);
        visit.push_back(cur[1]);
        visit.push_back(cur[2]);
      }
      else
      {
        // leaf, make equal
        Assert (cur.getType().isComparableTo(lhs.getType()));
        visited[cur] = cur.eqNode(lhs);
      }
    } else if (it->second.isNull()) {
      Assert (cur.getKind()==ITE);
      std::vector<Node> children;
      children.push_back(cur[0]);
      for (size_t i=1; i<=2; i++) {
        Node cn = cur[i];
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        children.push_back(it->second);
      }
      // always changes
      visited[cur] = nm->mkNode(ITE, children);
    }
  } while (!visit.empty());
  Assert(visited.find(ite) != visited.end());
  Assert(!visited.find(ite)->second.isNull());
  return visited[ite];
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
