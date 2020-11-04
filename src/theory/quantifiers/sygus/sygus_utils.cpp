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

#include "expr/node_algorithm.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * Attribute for specifying a solution for a function-to-synthesize. This is
 * used for marking certain functions that we have solved for, e.g. during
 * preprocessing.
 */
struct SygusSolutionAttributeId
{
};
typedef expr::Attribute<SygusSolutionAttributeId, Node> SygusSolutionAttribute;

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

Node mkSygusConjecture(const std::vector<Node>& fs,
                       Node conj,
                       const Subs& solvedf)
{
  Assert(!fs.empty());
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> iattrs;
  // take existing properties, without the previous solves
  SygusSolutionAttribute ssa;
  // add the current solves, which should be a superset of the previous ones
  for (size_t i = 0, nsolved = solvedf.size(); i < nsolved; i++)
  {
    Node eq = solvedf.getEquality(i);
    Node var = nm->mkSkolem("solved", nm->booleanType());
    var.setAttribute(ssa, eq);
    Node ipv = nm->mkNode(INST_ATTRIBUTE, var);
    iattrs.push_back(ipv);
  }
  return mkSygusConjecture(fs, conj, iattrs);
}

void decomposeSygusConjecture(Node q,
                              std::vector<Node>& fs,
                              std::vector<Node>& unsf,
                              Subs& solvedf)
{
  Assert(q.getKind() == FORALL);
  Assert(q.getNumChildren() == 3);
  Node ipl = q[2];
  Assert(ipl.getKind() == INST_PATTERN_LIST);
  fs.insert(fs.end(), q[0].begin(), q[0].end());
  SygusSolutionAttribute ssa;
  for (const Node& ip : ipl)
  {
    if (ip.getKind() == INST_ATTRIBUTE)
    {
      Node ipv = ip[0];
      // does it specify a sygus solution?
      if (ipv.hasAttribute(ssa))
      {
        Node eq = ipv.getAttribute(ssa);
        Assert(std::find(fs.begin(), fs.end(), eq[0]) != fs.end());
        solvedf.addEquality(eq);
      }
    }
  }
  // add to unsolved functions
  for (const Node& f : fs)
  {
    if (!solvedf.contains(f))
    {
      unsf.push_back(f);
    }
  }
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

Node wrapSolutionForSynthFun(Node f, Node sol)
{
  Node al = getSygusArgumentListForSynthFun(f);
  if (!al.isNull())
  {
    sol = NodeManager::currentNM()->mkNode(LAMBDA, al, sol);
  }
  Assert(!expr::hasFreeVar(sol));
  return sol;
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

bool isSingleInvocationType(const std::vector<Node>& fs)
{
  Assert (!fs.empty());
  // just make free variables, assuming that all functions have same type
  TypeNode tn = fs[0].getType();
  for (size_t i=1, nfs = fs.size(); i<nfs; i++)
  {
    if (fs[i].getType()!=tn)
    {
      return false;
    }
  }
  return true;
}

bool isSingleInvocation(const std::vector<Node>& fs, Node conj, std::map<Node, Node>& ffs, std::vector<Node>& args)
{
  Assert (isSingleInvocationType(fs));
  bool argsSet = false;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::unordered_set<TNode, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(conj);
  do {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end()) {
      visited.insert(cur);
      // if it is a function-to-synthesize
      if (std::find(fs.begin(),fs.end(),cur)!=fs.end())
      {
        if (cur.getType().isFunction())
        {
          // higher-order instance, always fail
          return false;
        }
        // corner case of constant function-to-synthesize
        ffs[cur] = cur;
      }
      else if (cur.getKind()==APPLY_UF)
      {
        Node op = cur.getOperator();
        // if it is a function we care about
        if (std::find(fs.begin(),fs.end(),op)!=fs.end())
        {
          Assert (!argsSet || cur.getNumChildren()==args.size());
          for (size_t i=0, nchild = cur.getNumChildren(); i<nchild; i++)
          {
            if (argsSet)
            {
              if (cur[i]!=args[i])
              {
                // different arguments
                return false;
              }
            }
            else
            {
              // not applied to bound variable
              if (cur[i].getKind()!=BOUND_VARIABLE)
              {
                return false;
              }
              args.push_back(cur[i]);
            }
          }
          // update the map
          if (ffs.find(op)==ffs.end())
          {
            ffs[op] = cur;
          }
          argsSet = true;
        }
      }
      visit.insert(visit.end(),cur.begin(),cur.end());
    }
  } while (!visit.empty());
  // add dummy arguments in the corner case that no functions appeared
  if (!argsSet)
  {
    TypeNode ft = fs[0].getType();
    if (ft.isFunction())
    {
      NodeManager * nm = NodeManager::currentNM();
      std::vector<TypeNode> argTypes = ft.getArgTypes();
      for (const TypeNode& at : argTypes)
      {
        args.push_back(nm->mkBoundVar(at));
      }
    }
  }
  return true;
}

bool isSingleInvocation(const std::vector<Node>& fs, Node conj, std::vector<Node>& args)
{
  std::map<Node, Node> ffs;
  return isSingleInvocation(fs, conj, ffs, args);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
