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
#include "expr/skolem_manager.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/datatypes/theory_datatypes_utils.h"
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
Node ElimTypesNodeConverter::postConvert(Node n, const std::vector<Node>& ncs)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  std::map<TypeNode, std::vector<TypeNode>>::iterator it;
  Kind k = n.getKind();
  if (n.isVar())
  {
    TypeNode tn = n.getType();
    if (tn.isConstructor() || tn.isSelector() || tn.isTester())
    {
      // don't bother converting these
      return Node::null();
    }
    TypeNode ctn = convertType(tn);
    if (tn != ctn)
    {
      if (k == BOUND_VARIABLE)
      {
        return nm->mkBoundVar(ctn);
      }
      std::stringstream ss;
      ss << n << "_pre";
      return sm->mkDummySkolem(ss.str(), ctn);
    }
    return Node::null();
  }
  else if (n.isClosure())
  {
    // inline arguments of the quantifier
    std::vector<Node> args(ncs[0].begin(), ncs[0].end());
    std::vector<Node> newArgs = inlineArguments(args);
    Node newBvl = nm->mkNode(BOUND_VAR_LIST, newArgs);
    std::vector<Node> ccs;
    ccs.push_back(newBvl);
    ccs.insert(ccs.end(), ncs.begin() + 1, ncs.end());
    return nm->mkNode(k, ccs);
  }
  if (k == EQUAL)
  {
    TypeNode tn = ncs[0].getType();
    it = d_splitDt.find(tn);
    if (it == d_splitDt.end())
    {
      // no change
      return Node::null();
    }
    // split into a conjunction
    const std::vector<Node>& ns0 = getOrMkSplitTerms(ncs[0]);
    const std::vector<Node>& ns1 = getOrMkSplitTerms(ncs[1]);
    Assert(ns0.size() == ns1.size());
    std::vector<Node> conj;
    for (size_t i = 0, nsize = ns0.size(); i < nsize; i++)
    {
      conj.push_back(ns0[i].eqNode(ns1[i]));
    }
    return nm->mkAnd(conj);
  }
  else if (k == APPLY_UF || k == APPLY_CONSTRUCTOR)
  {
    // inline arguments
    std::vector<Node> args(ncs.begin() + 1, ncs.end());
    std::vector<Node> newArgs = inlineArguments(args);
    if (args.size() == newArgs.size())
    {
      // arguments were not inlined
      return Node::null();
    }
    Node op = ncs[0];
    // replace constructor, if the return type changed
    if (k == APPLY_CONSTRUCTOR)
    {
      Assert(op == n.getOperator());
      TypeNode tn = n.getType();
      TypeNode ntn = convertType(tn);
      if (tn != ntn)
      {
        Assert(ntn.isDatatype());
        const DType& dt = ntn.getDType();
        size_t index = theory::datatypes::utils::indexOf(n.getOperator());
        op = dt[index].getConstructor();
      }
    }
    newArgs.insert(newArgs.begin(), op);
    return nm->mkNode(k, newArgs);
  }
  else if (k == APPLY_SELECTOR_TOTAL || k == APPLY_SELECTOR)
  {
    TypeNode tn = n[0].getType();
    it = d_splitDt.find(tn);
    if (it != d_splitDt.end())
    {
      // selector should already have been rewritten
      Assert(k != APPLY_SELECTOR);
      const std::vector<Node>& args = getOrMkSplitTerms(ncs[0]);
      size_t index = theory::datatypes::utils::indexOf(n.getOperator());
      Assert(0 <= index && index < args.size());
      return args[index];
    }
    // change the selector, if the argument has changed types
    TypeNode ntn = ncs[0].getType();
    if (tn != ntn)
    {
      Assert(ntn.isDatatype());
      const DType& dt = ntn.getDType();
      size_t cindex = theory::datatypes::utils::cindexOf(n.getOperator());
      size_t index = theory::datatypes::utils::indexOf(n.getOperator());
      return nm->mkNode(k, dt[cindex].getSelectorInternal(ntn, index), ncs[0]);
    }
  }
  else if (k == APPLY_TESTER)
  {
    Assert(d_splitDt.find(n.getType()) == d_splitDt.end());
    TypeNode ntn = ncs[0].getType();
    // change the tester, if the argument has changed types
    if (n[0].getType() != ntn)
    {
      Assert(ntn.isDatatype());
      const DType& dt = ntn.getDType();
      size_t index = theory::datatypes::utils::indexOf(n.getOperator());
      return nm->mkNode(APPLY_TESTER, dt[index].getTester(), ncs[0]);
    }
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
    std::vector<TypeNode> oldTypes;
    oldTypes.push_back(tn);

    std::vector<DType> newDts;
    newDts.push_back(DType(dt.getName()));
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
      newDts.back().addConstructor(newC);
    }
    if (fieldChanged)
    {
      std::vector<TypeNode> newTypes = nm->mkMutualDatatypeTypes(newDts);
      // TODO: cache all oldTypes -> newTypes
      return newTypes[0];
    }
  }
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
        // must look up the conversion of the types
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
      // do not modify the range type here
      return nm->mkFunctionType(newArgTypes, tn.getRangeType());
    }
  }
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

const std::vector<Node>& ElimTypesNodeConverter::getOrMkSplitTerms(Node n)
{
  std::map<Node, std::vector<Node>>::iterator it = d_splitDtTerms.find(n);
  if (it != d_splitDtTerms.end())
  {
    return it->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  TypeNode tn = n.getType();
  Assert(tn.isDatatype());
  Assert(d_splitDt.find(tn) != d_splitDt.end());
  const DType& dt = tn.getDType();
  const DTypeConstructor& dtc = dt[0];
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  std::vector<Node>& splitn = d_splitDtTerms[n];
  for (size_t i = 0, nargs = dtc.getNumArgs(); i < nargs; i++)
  {
    Node sk;
    if (k == BOUND_VARIABLE)
    {
      // can't use mkPurifySkolem
      sk = nm->mkBoundVar(dt[0].getArgType(i));
    }
    else
    {
      Node nc =
          nm->mkNode(APPLY_SELECTOR_TOTAL, dt[0].getSelectorInternal(tn, i), n);
      sk = sm->mkPurifySkolem(nc, "ke");
    }
    splitn.push_back(sk);
  }
  return splitn;
}

std::vector<Node> ElimTypesNodeConverter::inlineArguments(
    const std::vector<Node>& args)
{
  std::vector<Node> newArgs;
  for (const Node& n : args)
  {
    TypeNode tn = n.getType();
    if (d_splitDt.find(tn) == d_splitDt.end())
    {
      // not inlined
      newArgs.push_back(n);
      continue;
    }
    const std::vector<Node>& ns = getOrMkSplitTerms(n);
    newArgs.insert(newArgs.end(), ns.begin(), ns.end());
  }
  return newArgs;
}

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
    Node ac = d_etnc.convert((*assertionsToPreprocess)[i]);
    ac = Rewriter::rewrite(ac);
    assertionsToPreprocess->replace(i, ac);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
