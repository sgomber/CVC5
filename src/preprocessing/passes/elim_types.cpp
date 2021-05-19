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
  // Kind k = n.getKind();
  return Node::null();
}
Node ElimTypesNodeConverter::postConvert(Node n, const std::vector<Node>& ncs)
{
  Trace("elim-types-debug2")
      << "postConvert " << n << " / " << ncs << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  std::map<TypeNode, std::vector<TypeNode>>::iterator it;
  Kind k = n.getKind();
  if (n.isVar())
  {
    TypeNode tn = n.getType();
    if (tn.isConstructor() || tn.isTester() || tn.isSelector())
    {
      // don't bother converting these, they will be converted when we
      // deal with APPLY_CONSTRUCTOR / APPLY_TESTER
      return Node::null();
    }
    TypeNode ctn = convertType(tn);
    if (tn != ctn)
    {
      Trace("elim-types-debug") << "postConvert variable" << std::endl;
      if (k == BOUND_VARIABLE)
      {
        return nm->mkBoundVar(ctn);
      }
      std::stringstream ss;
      ss << n << "_elim";
      Node ret = sm->mkDummySkolem(ss.str(), ctn);
      return returnConvert(n, ret);
    }
    return Node::null();
  }
  else if (n.isClosure())
  {
    Trace("elim-types-debug") << "postConvert closure" << std::endl;
    // inline arguments of the quantifier
    std::vector<Node> args(ncs[0].begin(), ncs[0].end());
    std::vector<Node> newArgs = inlineArguments(args);
    Node newBvl = nm->mkNode(BOUND_VAR_LIST, newArgs);
    std::vector<Node> ccs;
    ccs.push_back(newBvl);
    ccs.insert(ccs.end(), ncs.begin() + 1, ncs.end());
    Node ret = nm->mkNode(k, ccs);
    return returnConvert(n, ret);
  }
  if (k == EQUAL)
  {
    AlwaysAssert(ncs[0].getType() == ncs[1].getType())
        << "Bad type equality " << ncs << " " << ncs[0].getType() << " / "
        << ncs[1].getType();
    TypeNode tn = ncs[0].getType();
    it = d_splitDt.find(tn);
    if (it == d_splitDt.end())
    {
      // no change
      return Node::null();
    }
    Trace("elim-types-debug") << "postConvert equal " << n << std::endl;
    // split into a conjunction
    const std::vector<Node>& ns0 = getOrMkSplitTerms(ncs[0]);
    const std::vector<Node>& ns1 = getOrMkSplitTerms(ncs[1]);
    Assert(ns0.size() == ns1.size());
    std::vector<Node> conj;
    for (size_t i = 0, nsize = ns0.size(); i < nsize; i++)
    {
      conj.push_back(ns0[i].eqNode(ns1[i]));
    }
    Node ret = nm->mkAnd(conj);
    return returnConvert(n, ret);
  }
  else if (k == APPLY_UF || k == APPLY_CONSTRUCTOR)
  {
    Trace("elim-types-debug") << "postConvert " << k << std::endl;
    // inline arguments
    std::vector<Node> args(ncs.begin() + 1, ncs.end());
    std::vector<Node> newArgs = inlineArguments(args);
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
        AlwaysAssert(dt[index].getNumArgs() == newArgs.size());
      }
    }
    newArgs.insert(newArgs.begin(), op);
    Node ret = nm->mkNode(k, newArgs);
    return returnConvert(n, ret);
  }
  else if (k == APPLY_SELECTOR)
  {
    Trace("elim-types-debug") << "postConvert " << k << std::endl;
    Assert(ncs.size() == 2);
    TypeNode tn = n[0].getType();
    // change the selector, if the argument has changed types
    TypeNode ntn = ncs[1].getType();
    if (tn != ntn)
    {
      Assert(ntn.isDatatype());
      const DType& dt = ntn.getDType();
      size_t cindex = theory::datatypes::utils::cindexOf(n.getOperator());
      Assert(0 <= cindex && cindex < dt.getNumConstructors());
      // must use mapped index, since argument index may be different in the new
      // datatype
      size_t index = getMappedDatatypeIndex(n.getOperator());
      Assert(0 <= index && index < dt[cindex].getNumArgs());
      // if we are splitting the return type, we must convert to a list of
      // selectors, packaged together with a constructor
      TypeNode rtn = n.getType();
      it = d_splitDt.find(rtn);
      if (it != d_splitDt.end())
      {
        rtn = convertType(rtn);
        Assert(rtn.isDatatype());
        const DType& rdt = rtn.getDType();
        Trace("elim-types-debug")
            << "...split return type " << rtn << std::endl;
        std::vector<Node> args;
        args.push_back(rdt[0].getConstructor());
        for (size_t i = 0, nargs = it->second.size(); i < nargs; i++)
        {
          Assert(index < dt[cindex].getNumArgs());
          Node sel = nm->mkNode(k, dt[cindex][index].getSelector(), ncs[1]);
          args.push_back(sel);
          index++;
        }
        Node ret = nm->mkNode(APPLY_CONSTRUCTOR, args);
        return returnConvert(n, ret);
      }
      Trace("elim-types-debug") << "...change selector " << rtn << std::endl;
      Node ret = nm->mkNode(k, dt[cindex][index].getSelector(), ncs[1]);
      return returnConvert(n, ret);
    }
    if (n[0].isVar())
    {
      it = d_splitDt.find(tn);
      // if we are splitting the argument type, (S_i x) ---> x_i
      // where x is a variable of a datatype we are splitting
      if (it != d_splitDt.end())
      {
        Trace("elim-types-debug") << "...split arg type " << tn << std::endl;
        const std::vector<Node>& args = getOrMkSplitTerms(ncs[1]);
        size_t index = getMappedDatatypeIndex(n.getOperator());
        Assert(0 <= index && index < args.size());
        Node ret = args[index];
        return returnConvert(n, ret);
      }
    }
    Trace("elim-types-debug") << "...no change " << tn << std::endl;
  }
  else if (k == APPLY_TESTER)
  {
    Trace("elim-types-debug") << "postConvert " << k << std::endl;
    Assert(d_splitDt.find(n.getType()) == d_splitDt.end());
    Assert(ncs.size() == 2);
    TypeNode ntn = ncs[1].getType();
    // change the tester, if the argument has changed types
    if (n[0].getType() != ntn)
    {
      Assert(ntn.isDatatype());
      const DType& dt = ntn.getDType();
      size_t index = theory::datatypes::utils::indexOf(n.getOperator());
      Node ret = nm->mkNode(APPLY_TESTER, dt[index].getTester(), ncs[1]);
      return returnConvert(n, ret);
    }
  }
  // should not have expanded apply selector total yet
  Assert(k != APPLY_SELECTOR_TOTAL);
  return Node::null();
}
TypeNode ElimTypesNodeConverter::postConvertType(TypeNode tn)
{
  NodeManager* nm = NodeManager::currentNM();
  std::map<TypeNode, std::vector<TypeNode>>::iterator it;
  if (tn.isDatatype())
  {
    // otherwise, convert and inline the subfield types
    const DType& dt = tn.getDType();
    // TODO: mutually recursive datatypes???
    // compute mutual block???
    // std::vector<TypeNode>& stypes = dt.getSubfieldTypes();
    std::vector<TypeNode> oldTypes;
    oldTypes.push_back(tn);
    Trace("elim-types") << "Datatype convert " << tn << std::endl;

    std::vector<DType> newDts;
    std::stringstream ssd;
    ssd << dt.getName() << "_elim";
    newDts.push_back(DType(ssd.str()));
    bool fieldChanged = false;
    for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      const DTypeConstructor& dtc = dt[i];
      std::stringstream ssc;
      ssc << dtc.getName() << "_elim";
      std::shared_ptr<DTypeConstructor> newC =
          std::make_shared<DTypeConstructor>(ssc.str());
      const std::vector<std::shared_ptr<DTypeSelector>>& args = dtc.getArgs();
      size_t nargs = 0;
      for (const std::shared_ptr<DTypeSelector>& a : args)
      {
        Trace("elim-types") << "...process " << a->getName() << std::endl;
        std::stringstream ss;
        ss << a->getName() << "_elim";
        TypeNode tna = a->getRangeType();
        // maintain mapping to corresponding index in new constructor
        d_dtIndex[a->getSelector()] = nargs;
        if (tn == tna)
        {
          // AlwaysAssert(false) << "recursive datatypes not handled";
          newC->addArgSelf(ss.str());
          // recursive, add self?
          continue;
        }
        it = d_splitDt.find(tna);
        if (it != d_splitDt.end())
        {
          Trace("elim-types") << "...inline" << std::endl;
          for (size_t j = 0, ntypes = it->second.size(); j < ntypes; j++)
          {
            std::stringstream sse;
            sse << ss.str() << "_" << j;
            newC->addArg(sse.str(), convertType(it->second[j]));
            nargs++;
          }
          fieldChanged = true;
        }
        else
        {
          Trace("elim-types") << "...map: selector " << a->getSelector()
                              << " -> " << nargs << std::endl;
          TypeNode tnaNew = convertType(tna);
          newC->addArg(ss.str(), tnaNew);
          fieldChanged = fieldChanged || tnaNew != tna;
          nargs++;
        }
      }
      newDts.back().addConstructor(newC);
    }
    Trace("elim-types") << "...finished datatype convert, fieldChanged = "
                        << fieldChanged << std::endl;
    if (fieldChanged)
    {
      std::vector<TypeNode> newTypes = nm->mkMutualDatatypeTypes(newDts);
      if (d_splitDt.find(tn) != d_splitDt.end())
      {
        addElimDatatype(newTypes[0]);
      }
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
  NodeManager* nm = NodeManager::currentNM();
  Assert(dtn.isDatatype());
  const DType& dt = dtn.getDType();
  Assert(dt.getNumConstructors() == 1);
  const DTypeConstructor& dtc = dt[0];
  std::vector<TypeNode>& ts = d_splitDt[dtn];
  // std::vector<Node>& sels = d_splitDtSelc[dtn];
  Node x = nm->mkBoundVar(dtn);
  Node bvlx = nm->mkNode(BOUND_VAR_LIST, x);
  for (unsigned j = 0, nargs = dtc.getNumArgs(); j < nargs; ++j)
  {
    TypeNode tn = dtc.getArgType(j);
    Node selOp = dtc[j].getSelector();
    Node sel = nm->mkNode(APPLY_SELECTOR, selOp, x);
    // recursively inline
    if (tn.isDatatype())
    {
      const DType& dta = tn.getDType();
      if (dta.getNumConstructors() == 1)
      {
        addElimDatatype(tn);
        std::vector<TypeNode>& tsa = d_splitDt[dtn];
        ts.insert(ts.end(), tsa.begin(), tsa.end());
        /*
        std::vector<Node>& sela = d_splitDtSelc[dtn];
        for (const Node& sa : sela)
        {
          Node chain = nm->mkNode(APPLY_UF, sa, sel);
          chain = Rewriter::rewrite(chain);
          chain = nm->mkNode(LAMBDA, bvlx, chain);
          sels.push_back(chain);
        }
        */
        continue;
      }
    }
    ts.push_back(tn);
    sel = nm->mkNode(LAMBDA, bvlx, sel);
    // sels.push_back(sel);
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
  Trace("elim-types-debug")
      << "getOrMkSplitTerms " << n << " : " << tn << std::endl;
  Assert(tn.isDatatype());
  Assert(d_splitDt.find(tn) != d_splitDt.end());
  std::vector<TypeNode>& stypes = d_splitDt[tn];
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  std::vector<Node>& splitn = d_splitDtTerms[n];
  Node op;
  if (k == APPLY_UF)
  {
    // FIXME: probably not right for apply selector
    // if f(t), split to f1(t) ... fn(t)
    op = n.getOperator();
    it = d_splitDtTerms.find(op);
    if (it == d_splitDtTerms.end())
    {
      d_splitDtTerms[op].clear();
      it = d_splitDtTerms.find(op);
      std::vector<TypeNode> fargs;
      for (const Node& nc : n)
      {
        fargs.push_back(convertType(nc.getType()));
      }
      for (size_t i = 0, nargs = stypes.size(); i < nargs; i++)
      {
        TypeNode ftn = nm->mkFunctionType(fargs, stypes[i]);
        std::stringstream ss;
        ss << "keo_" << op << "_" << i;
        Node sko = sm->mkDummySkolem(ss.str(), ftn);
        it->second.push_back(sko);
      }
    }
    for (size_t i = 0, nargs = stypes.size(); i < nargs; i++)
    {
      std::vector<Node> elimChildren{it->second[i]};
      elimChildren.insert(elimChildren.end(), n.begin(), n.end());
      Node sk = nm->mkNode(APPLY_UF, elimChildren);
      splitn.push_back(sk);
    }
  }
  else if (k == APPLY_CONSTRUCTOR)
  {
    // C(t1...tn) becomes s1 ... sm, for recursively inlined t1 ... tn
    for (const Node& nc : n)
    {
      TypeNode tnc = nc.getType();
      if (d_splitDt.find(tnc) == d_splitDt.end())
      {
        splitn.push_back(nc);
        continue;
      }
      const std::vector<Node>& splitc = getOrMkSplitTerms(nc);
      splitn.insert(splitn.end(), splitc.begin(), splitc.end());
    }
    Assert(splitn.size() == stypes.size());
  }
  else if (k == ITE)
  {
    // (ite A t1 t2) becomes (ite A k11 k21) .... (ite A k1n k2n)
    const std::vector<Node>& ns1 = getOrMkSplitTerms(n[1]);
    const std::vector<Node>& ns2 = getOrMkSplitTerms(n[2]);
    Assert(ns1.size() == ns2.size());
    for (size_t i = 0, nsize = ns1.size(); i < nsize; i++)
    {
      splitn.push_back(nm->mkNode(ITE, n[0], ns1[i], ns2[i]));
    }
  }
  else
  {
    AlwaysAssert(n.isVar()) << "Cannot split " << n;
    for (size_t i = 0, nargs = stypes.size(); i < nargs; i++)
    {
      TypeNode stc = convertType(stypes[i]);
      Node sk;
      if (k == BOUND_VARIABLE)
      {
        // can't use mkPurifySkolem
        sk = nm->mkBoundVar(stc);
      }
      else
      {
        std::stringstream ss;
        ss << "ke_" << n << "_" << i;
        sk = sm->mkDummySkolem(ss.str(), stc);
      }
      splitn.push_back(sk);
    }
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
size_t ElimTypesNodeConverter::getMappedDatatypeIndex(Node op) const
{
  std::map<Node, size_t>::const_iterator it = d_dtIndex.find(op);
  Assert(it != d_dtIndex.end());
  return it->second;
}

Node ElimTypesNodeConverter::returnConvert(Node n, Node ret)
{
  TypeNode tn = n.getType();
  TypeNode tnr = ret.getType();
  Trace("elim-types-debug") << "...return " << ret << std::endl;
  AlwaysAssert(tn.isSelector() || convertType(tn) == tnr)
      << "...bad conversion " << n << " -> " << ret << ", types " << tn
      << " -> " << tnr << ", expected " << convertType(tn);
  return ret;
}

ElimTypes::ElimTypes(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "elim-types")
{
}

void ElimTypes::collectTypes(
    const Node& n,
    std::unordered_set<TNode>& visited,
    std::unordered_set<TypeNode>& types)
{
  std::unordered_set<TNode>::iterator it;
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
  Trace("elim-types") << "ElimTypes: collect types..." << std::endl;
  // Step 1: infer types to eliminate
  std::unordered_set<TNode> visited;
  std::unordered_set<TypeNode> types;
  size_t nasserts = assertionsToPreprocess->size();
  for (size_t i = 0; i < nasserts; ++i)
  {
    collectTypes((*assertionsToPreprocess)[i], visited, types);
  }

  Trace("elim-types") << "ElimTypes: compute types..." << std::endl;
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
      Trace("elim-types") << "...eliminate " << p.first << std::endl;
      // mark as eliminated
      d_etnc.addElimDatatype(p.first);
    }
  }

  if (d_etnc.empty())
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }

  Trace("elim-types") << "ElimTypes: simplify..." << std::endl;
  // Step 2: simplify
  for (size_t i = 0; i < nasserts; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    Node ac = d_etnc.convert(prev);
    ac = Rewriter::rewrite(ac);
    /*
    if (expr::hasFreeVar(ac))
    {
      std::unordered_set<Node> fvs;
      expr::getFreeVariables(ac, fvs);
      std::stringstream ss;
      for (const Node& v : fvs)
      {
        ss << v << " ";
      }
      AlwaysAssert(false) << "Converted " << ac << " from " << prev << " has
    free variables " << ss.str();
    }
    */
    assertionsToPreprocess->replace(i, ac);
  }

  Trace("elim-types") << "ElimTypes: finished" << std::endl;
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
