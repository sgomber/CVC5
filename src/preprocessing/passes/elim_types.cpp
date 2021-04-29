/******************************************************************************
 * Top contributors (to cur version):
 *   Yoni Zohar, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The foreign_theory_rewrite preprocessing pass.
 *
 * Simplifies nodes of one theory using rewrites from another.
 */

#include "preprocessing/passes/foreign_theory_rewrite.h"

#include "expr/node_traversal.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/rewriter.h"
#include "theory/strings/arith_entail.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

using namespace cvc5::theory;
ElimTypes::ElimTypes(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "foreign-theory-rewrite"),
      d_cache(preprocContext->getUserContext()){};

void ElimTypes::collectTypes(const Node& n, std::unordered_set<TNode, TNodeHashFunction>& visited, std::unordered_set<TypeNode, TypeNodeHashFunction>& types, std::map<TypeNode, std::vector<Node>>& syms)
{
  std::unordered_set<TNode, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end()) {
      visited.insert(cur);
      TypeNode tn = cur.getType();
      // remember type of all subterms
      types.insert(tn);
      if (cur.isVar())
      {
        syms[tn].push_back(cur);
      }
      else if (cur.getKind()==APPLY_UF)
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(),cur.begin(),cur.end());
    }
  } while (!visit.empty());
}

PreprocessingPassResult ElimTypes::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::unordered_set<TypeNode, TypeNodeHashFunction> types;
  std::map<TypeNode, std::vector<Node>> syms;
  size_t nasserts = assertionsToPreprocess->size();
  for (size_t i = 0; i < nasserts; ++i)
  {
    collectTypes((*assertionsToPreprocess)[i], visited, syms);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
