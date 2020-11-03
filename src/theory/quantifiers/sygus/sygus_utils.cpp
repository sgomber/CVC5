/*********************                                                        */
/*! \file sygus_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief generic sygus utilities
 **/

#include "theory/quantifiers/sygus/sygus_utils.h"

#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Node mkSygusConjecture(const std::vector<Node>& fs,
                       Node conj,
                       const std::vector<Node>& iattrs)
{
  Assert(!fs.empty());
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> ipls;
  SygusAttribute ca;
  Node sygusVar = nm->mkSkolem("sygus", nm->booleanType());
  sygusVar.setAttribute(ca, true);
  Node instAttr = nm->mkNode(INST_ATTRIBUTE, sygusVar);
  ipls.push_back(instAttr);
  // insert the remaining instantiation attributes
  ipls.insert(ipls.end(), iattrs.begin(), iattrs.end());
  Node ipl = nm->mkNode(INST_PATTERN_LIST, ipls);
  Node bvl = nm->mkNode(BOUND_VAR_LIST, fs);
  return nm->mkNode(FORALL, bvl, conj, ipl);
}

Node mkSygusConjecture(const std::vector<Node>& fs, Node conj)
{
  std::vector<Node> iattrs;
  return mkSygusConjecture(fs, conj, iattrs);
}

Node getSygusArgumentListForSynthFun(Node f)
{
  Node sfvl = f.getAttribute(SygusSynthFunVarListAttribute());
  if (sfvl.isNull() && f.getType().isFunction())
  {
    NodeManager* nm = NodeManager::currentNM();
    std::vector<TypeNode> argTypes = f.getType().getArgTypes();
    // make default variable list if none was specified by input
    std::vector<Node> bvs;
    for (unsigned j = 0, size = argTypes.size(); j < size; j++)
    {
      std::stringstream ss;
      ss << "arg" << j;
      bvs.push_back(nm->mkBoundVar(ss.str(), argTypes[j]));
    }
    sfvl = nm->mkNode(BOUND_VAR_LIST, bvs);
    f.setAttribute(SygusSynthFunVarListAttribute(), sfvl);
  }
  return sfvl;
}

void getSygusArgumentListForSynthFun(Node f, std::vector<Node>& formals)
{
  Node sfvl = getSygusArgumentListForSynthFun(f);
  if (!sfvl.isNull())
  {
    formals.insert(formals.end(), sfvl.begin(), sfvl.end());
  }
}

TypeNode getSygusTypeForSynthFun(Node f)
{
  Node gv = f.getAttribute(SygusSynthGrammarAttribute());
  if (!gv.isNull())
  {
    return gv.getType();
  }
  return TypeNode::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
