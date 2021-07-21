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
 * Rewriting based on learned literals
 */

#include "preprocessing/passes/analyze.h"

#include "preprocessing/assertion_pipeline.h"
#include "util/bitvector.h"

using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace preprocessing {
namespace passes {

Analyze::Analyze(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "analyze")
{
}

PreprocessingPassResult Analyze::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::unordered_set<TNode> visited;
  size_t size = assertionsToPreprocess->size();
  for (size_t i = 0; i < size; ++i)
  {
    Node n = (*assertionsToPreprocess)[i];
    analyze(n, visited);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

void Analyze::analyze(Node n,
                         std::unordered_set<TNode>& visited)
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
    if (it != visited.end())
    {
      continue;
    }
    visited.insert(cur);
    visit.insert(visit.end(), cur.begin(), cur.end());
    Kind k = cur.getKind();
    if (k==CONST_BITVECTOR)
    {
      
    }
  } while (!visit.empty());
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
