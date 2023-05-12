/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Apply substitutions preprocessing pass.
 *
 * Apply top level substitutions to assertions, rewrite, and store back into
 * assertions.
 */

#include "preprocessing/passes/assigner_infer.h"

#include "expr/assigner.h"
#include "expr/skolem_manager.h"
#include "options/theory_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/env.h"
#include "expr/node_algorithm.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

AssignerInfer::AssignerInfer(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "assigner-infer"),
      d_numAssigners(
          statisticsRegistry().registerInt("AssignerInfer::numAssigners"))
{
}

PreprocessingPassResult AssignerInfer::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  size_t size = assertionsToPreprocess->size();
  std::vector<Node> lemmas;
  std::unordered_map<TNode, Node> visited;
  for (size_t i = 0; i < size; ++i)
  {
    const Node& assertion = (*assertionsToPreprocess)[i];
    const Node& aa = convertToAssigner(visited, assertion, lemmas);
    if (aa != assertion)
    {
      assertionsToPreprocess->replace(i, aa);
    }
  }
  if (!lemmas.empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    Node newAssertion = nm->mkAnd(lemmas);
    assertionsToPreprocess->push_back(newAssertion);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

Node AssignerInfer::convertToAssigner(std::unordered_map<TNode, Node> visited,
                                      const Node& n,
                                      std::vector<Node>& lemmas)
{
  NodeManager* nm = NodeManager::currentNM();
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
      if (expr::isBooleanConnective(cur))
      {
        // if assigner, register to node manager, and replace by its assigner
        // variable
        if (Assigner::isAssigner(cur))
        {
          d_numAssigners++;
          Assigner* a = d_env.registerAssigner(cur);
          Assert(a != nullptr);
          Node lit = a->getSatLiteral();
          Trace("assigner")
              << "Found assigner: " << lit << " <=> " << cur << std::endl;
          visited[cur] = lit;
          Node conc = cur;
          if (options().theory.assignerProxy)
          {
            SkolemManager* skm = nm->getSkolemManager();
            std::vector<Node> cdisj;
            for (const Node& cc : cur)
            {
              Assert(cc.getKind() != kind::NOT);
              cdisj.push_back(skm->mkProxyLit(cc));
            }
            conc = nm->mkOr(cdisj);
          }
          Node lem = nm->mkNode(kind::EQUAL, lit, conc);
          lemmas.emplace_back(lem);
        }
        else
        {
          visited[cur] = Node::null();
          visit.push_back(cur);
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
        continue;
      }
      visited[cur] = cur;
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
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
