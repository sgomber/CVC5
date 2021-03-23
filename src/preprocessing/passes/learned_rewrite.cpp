/*********************                                                        */
/*! \file learned_rewrite.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Caleb Donovick
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriting based on learned literals
 **/

#include "preprocessing/passes/learned_rewrite.h"

#include "expr/skolem_manager.h"
#include "expr/term_context_stack.h"
#include "theory/rewriter.h"
#include "preprocessing/assertion_pipeline.h"

using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {

LearnedRewrite::LearnedRewrite(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "learned-rewrite"){};

PreprocessingPassResult LearnedRewrite::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  arith::BoundInference binfer;
  std::vector<Node>& learnedLits = d_preprocContext->getLearnedLiterals();
  if (learnedLits.empty())
  {
    Trace("learned-rewrite-ll") << "No learned literals" << std::endl;
  }
  else
  {
    Trace("learned-rewrite-ll") << "Learned literals:" << std::endl;
    for (const Node& l : learnedLits)
    {
      Node e = rewriteLearnedRec(l, binfer);
      // maybe for bound inference?
      Kind k = e.getKind();
      if (k == EQUAL || k == GEQ)
      {
        binfer.add(e);
      }
      Trace("learned-rewrite-ll") << "- " << e << std::endl;
    }
  }
  size_t size = assertionsToPreprocess->size();
  for (size_t i = 0; i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    Trace("learned-rewrite-assert")
        << "LearnedRewrite: assert: " << prev << std::endl;
    Node e = rewriteLearnedRec(prev, binfer);
    if (e != prev)
    {
      Trace("learned-rewrite-assert")
          << ".......................: " << e << std::endl;
      assertionsToPreprocess->replace(i, e);
    }
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

Node LearnedRewrite::rewriteLearnedRec(Node n, arith::BoundInference& binfer)
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
      bool needsRcons = false;
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
        needsRcons = needsRcons || cn != it->second;
        children.push_back(it->second);
      }
      if (needsRcons)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      // rewrite here
      ret = rewriteLearned(ret, binfer);
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node LearnedRewrite::rewriteLearned(Node n,
                                    theory::arith::BoundInference& binfer)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("learned-rewrite-rr-debug") << "Rewrite " << n << std::endl;
  Node nr = Rewriter::rewrite(n);
  Kind k = nr.getKind();
  if (k == INTS_DIVISION || k == INTS_MODULUS || k == DIVISION)
  {
    // simpler if we know the divisor is non-zero
    Node num = n[0];
    Node den = n[1];
    bool isNonZeroDen = false;
    if (den.isConst())
    {
      isNonZeroDen = (den.getConst<Rational>().sgn() != 0);
    }
    else
    {
      arith::Bounds db = binfer.get(den);
      Trace("learned-rewrite-rr-debug")
          << "Bounds for " << den << " : " << db.lower_bound << " "
          << db.upper_bound << std::endl;
      if (!db.lower_bound.isNull()
          && db.lower_bound.getConst<Rational>().sgn() == 1)
      {
        isNonZeroDen = true;
      }
      else if (!db.upper_bound.isNull()
               && db.upper_bound.getConst<Rational>().sgn() == -1)
      {
        isNonZeroDen = true;
      }
    }
    if (isNonZeroDen)
    {
      Trace("learned-rewrite-rr-debug")
          << "...non-zero denominator" << std::endl;
      Kind nk = k;
      switch (k)
      {
        case INTS_DIVISION: nk = INTS_DIVISION_TOTAL; break;
        case INTS_MODULUS: nk = INTS_MODULUS_TOTAL; break;
        case DIVISION: nk = DIVISION_TOTAL; break;
        default: Assert(false); break;
      }
      std::vector<Node> children;
      children.insert(children.end(), n.begin(), n.end());
      nr = nm->mkNode(nk, children);
      Trace("learned-rewrite-rr")
          << "LearnedRewrite::Rewrite : " << n << " == " << nr << std::endl;
      nr = Rewriter::rewrite(nr);
    }
  }
  // constant int div / mod elimination by bound inference
  if (k == INTS_DIVISION_TOTAL || k == INTS_MODULUS_TOTAL)
  {
    Node num = n[0];
    Node den = n[1];
    if (den.isConst())
    {
      arith::Bounds db = binfer.get(num);
    }
  }
  return nr;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
