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
 * The eliminate types preprocessing pass.
 */

#include "preprocessing/passes/elim_types.h"

#include <sstream>

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
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

Node ElimTypesNodeConverter::preConvert(Node n)
{
  if (n.isClosure())
  {
    for (const Node& v : n[0])
    {
    }
  }
  // Kind k = n.getKind();
  return Node::null();
}
Node ElimTypesNodeConverter::postConvert(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  std::map<TypeNode, std::vector<TypeNode>>::iterator it;
  Kind k = n.getKind();
  if (n.isVar())
  {
    TypeNode tn = n.getType();
    TypeNode ctn = convertType(tn);
    if (tn != ctn)
    {
      // convert to pre-type
      std::stringstream ss;
      ss << n << "_pre";
      // return nm->mkSkolem(ss.str(), ctn);
    }
    return Node::null();
  }
  else if (n.isClosure())
  {
    // inline 
  }
  if (k == EQUAL)
  {
    TypeNode tn = n[0].getType();
    it = d_splitDt.find(tn);
    if (it != d_splitDt.end())
    {
      // split into a conjunction TODO
    }
  }
  else if (k == APPLY_UF)
  {
    // inline arguments
  }
  else if (k == APPLY_CONSTRUCTOR)
  {
    // if the type changed
  }
  else if (k == APPLY_SELECTOR_TOTAL || k==APPLY_SELECTOR)
  {
  }
  else if (k == APPLY_TESTER)
  {
    // if the type changed
  }
  return Node::null();
}
TypeNode ElimTypesNodeConverter::postConvertType(TypeNode tn)
{
  NodeManager* nm = NodeManager::currentNM();
  std::map<TypeNode, std::vector<TypeNode>>::iterator it;
  if (tn.isDatatype())
  {
    it = d_splitDt.find(tn);
    if (it != d_splitDt.end())
    {
      // do not modify datatypes we are splitting
      return TypeNode::null();
    }
    // otherwise, convert and inline the subfield types
    const DType& dt = tn.getDType();
    // TODO: mutually recursive datatypes???
    // compute mutual block???
    // std::vector<TypeNode>& stypes = dt.getSubfieldTypes();

    DType newDt(dt.getName());
    bool fieldChanged = false;
    for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      const DTypeConstructor& dtc = dt[i];
      std::shared_ptr<DTypeConstructor> newC =
          std::make_shared<DTypeConstructor>(dtc.getName());
      const std::vector<std::shared_ptr<DTypeSelector>>& args = dtc.getArgs();
      for (const std::shared_ptr<DTypeSelector>& a : args)
      {
        TypeNode tna = a->getRangeType();
        if (tn == tna)
        {
          // recursive, add self?
          continue;
        }
        it = d_splitDt.find(tna);
        if (it != d_splitDt.end())
        {
          for (size_t j = 0, ntypes = it->second.size(); j < ntypes; j++)
          {
            std::stringstream ss;
            ss << a->getName() << "_" << j;
            newC->addArg(ss.str(), convertType(it->second[j]));
          }
          fieldChanged = true;
        }
        else
        {
          TypeNode tnaNew = convertType(tna);
          newC->addArg(a->getName(), tnaNew);
          fieldChanged = fieldChanged || tnaNew != tna;
        }
      }
      newDt.addConstructor(newC);
    }
    if (fieldChanged)
    {
      // TODO
    }
  }
  /*
  else if (tn.isFunction())
  {
    // inline argument functions
    std::vector<TypeNode> argTypes = tn.getArgTypes();
    bool argTypeChanged = false;
    std::vector<TypeNode> newArgTypes;
    for (const TypeNode& tna : argTypes)
    {
      it = d_splitDt.find(tna);
      if (it != d_splitDt.end())
      {
        for (size_t i = 0, ntypes = it->second.size(); i < ntypes; i++)
        {
          newArgTypes.push_back(convertType(it->second[i]));
        }
        argTypeChanged = true;
      }
      else
      {
        newArgTypes.push_back(tna);
      }
    }
    if (argTypeChanged)
    {
      // do not modify the range type
      return nm->mkFunctionType(newArgTypes, tn.getRangeType());
    }
  }
  */
  return TypeNode::null();
}

void ElimTypesNodeConverter::addElimDatatype(TypeNode dtn)
{
  if (d_splitDt.find(dtn) != d_splitDt.end())
  {
    // already registered
    return;
  }
  Assert(dtn.isDatatype());
  const DType& dt = dtn.getDType();
  Assert(dt.getNumConstructors() == 1);
  const DTypeConstructor& dtc = dt[0];
  std::vector<TypeNode>& ts = d_splitDt[dtn];
  for (unsigned j = 0, nargs = dtc.getNumArgs(); j < nargs; ++j)
  {
    ts.push_back(dtc.getArgType(j));
  }
}
bool ElimTypesNodeConverter::empty() const { return d_splitDt.empty(); }

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

  if (d_etnc.empty())
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
