/******************************************************************************
 * Top contributors (to cur version):
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
 * The eliminate types preprocessing pass.
 */

#include "preprocessing/passes/elim_types.h"

#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "expr/node_traversal.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/rewriter.h"

using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace preprocessing {
namespace passes {

  Node ElimTypesNodeConverter::preConvert(Node n) { return Node::null(); }
  Node ElimTypesNodeConverter::postConvert(Node n) { return Node::null(); }
  TypeNode ElimTypesNodeConverter::postConvertType(TypeNode n) { return TypeNode::null(); }

  void ElimTypesNodeConverter::addElimDatatype(TypeNode dtn){}
  
ElimTypes::ElimTypes(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "elim-types")
{
}

void ElimTypes::collectTypes(
    const Node& n,
    std::unordered_set<TNode, TNodeHashFunction>& visited,
    std::unordered_set<TypeNode, TypeNodeHashFunction>& types,
    std::map<TypeNode, std::vector<Node>>& syms)
{
  std::unordered_set<TNode, TNodeHashFunction>::iterator it;
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
      visited.insert(cur);
      TypeNode tn = cur.getType();
      // remember type of all subterms, and get all their component types,
      // where we additional traverse datatype subfield types
      expr::getComponentTypes(tn, types, true);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

PreprocessingPassResult ElimTypes::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // Step 1: infer types to eliminate
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::unordered_set<TypeNode, TypeNodeHashFunction> types;
  std::map<TypeNode, std::vector<Node>> syms;
  size_t nasserts = assertionsToPreprocess->size();
  for (size_t i = 0; i < nasserts; ++i)
  {
    collectTypes((*assertionsToPreprocess)[i], visited, types, syms);
  }

  std::map<TypeNode, bool> shouldElimType;
  for (const TypeNode& tn : types)
  {
    if (tn.isDatatype())
    {
      const DType& dt = tn.getDType();
      if (dt.getNumConstructors() == 1)
      {
        if (shouldElimType.find(tn) == shouldElimType.end())
        {
          shouldElimType[tn] = true;
        }
      }
    }
    else if (tn.isSet() || tn.isBag() || tn.isArray())
    {
      // child types of these cannot be eliminated currently
      for (const TypeNode& tnc : tn)
      {
        shouldElimType[tnc] = false;
      }
    }
  }
  for (const std::pair<const TypeNode, bool>& p : shouldElimType)
  {
    if (p.second)
    {
      // mark as eliminated
      d_etnc.addElimDatatype(p.first);
    }
  }

  if (d_typeCache.empty())
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }

  // Step 2: simplify
  for (size_t i = 0; i < nasserts; ++i)
  {
    assertionsToPreprocess->replace(
        i, Rewriter::rewrite(d_etnc.convert((*assertionsToPreprocess)[i])));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
