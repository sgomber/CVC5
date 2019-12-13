/*********************                                                        */
/*! \file codatatype_normalize.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of utility for normalizing codatatype constants.
 **/

#include "theory/datatypes/codatatype_normalize.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace datatypes {

Node CoDatatypeNormalize::normalizeCodatatypeConstant(Node n)
{
  Trace("dt-nconst") << "Normalize " << n << std::endl;
  std::map<Node, Node> rf;
  std::vector<Node> sk;
  std::vector<Node> rf_pending;
  std::vector<Node> terms;
  std::map<Node, bool> cdts;
  Node s = collectRef(n, sk, rf, rf_pending, terms, cdts);
  if (!s.isNull())
  {
    Trace("dt-nconst") << "...symbolic normalized is : " << s << std::endl;
    for (std::map<Node, Node>::iterator it = rf.begin(); it != rf.end(); ++it)
    {
      Trace("dt-nconst") << "  " << it->first << " = " << it->second
                         << std::endl;
    }
    // now run DFA minimization on term structure
    Trace("dt-nconst") << "  " << terms.size()
                       << " total subterms :" << std::endl;
    int eqc_count = 0;
    std::map<Node, int> eqc_op_map;
    std::map<Node, int> eqc;
    std::map<int, std::vector<Node> > eqc_nodes;
    // partition based on top symbol
    for (unsigned j = 0, size = terms.size(); j < size; j++)
    {
      Node t = terms[j];
      Trace("dt-nconst") << "    " << t << ", cdt=" << cdts[t] << std::endl;
      int e;
      if (cdts[t])
      {
        Assert(t.getKind() == kind::APPLY_CONSTRUCTOR);
        Node op = t.getOperator();
        std::map<Node, int>::iterator it = eqc_op_map.find(op);
        if (it == eqc_op_map.end())
        {
          e = eqc_count;
          eqc_op_map[op] = eqc_count;
          eqc_count++;
        }
        else
        {
          e = it->second;
        }
      }
      else
      {
        e = eqc_count;
        eqc_count++;
      }
      eqc[t] = e;
      eqc_nodes[e].push_back(t);
    }
    // partition until fixed point
    int eqc_curr = 0;
    bool success = true;
    while (success)
    {
      success = false;
      int eqc_end = eqc_count;
      while (eqc_curr < eqc_end)
      {
        if (eqc_nodes[eqc_curr].size() > 1)
        {
          // look at all nodes in this equivalence class
          unsigned nchildren = eqc_nodes[eqc_curr][0].getNumChildren();
          std::map<int, std::vector<Node> > prt;
          for (unsigned j = 0; j < nchildren; j++)
          {
            prt.clear();
            // partition based on children : for the first child that causes a
            // split, break
            for (unsigned k = 0, size = eqc_nodes[eqc_curr].size(); k < size;
                 k++)
            {
              Node t = eqc_nodes[eqc_curr][k];
              Assert(t.getNumChildren() == nchildren);
              Node tc = t[j];
              // refer to loops
              std::map<Node, Node>::iterator itr = rf.find(tc);
              if (itr != rf.end())
              {
                tc = itr->second;
              }
              Assert(eqc.find(tc) != eqc.end());
              prt[eqc[tc]].push_back(t);
            }
            if (prt.size() > 1)
            {
              success = true;
              break;
            }
          }
          // move into new eqc(s)
          for (const std::pair<const int, std::vector<Node> >& p : prt)
          {
            int e = eqc_count;
            for (unsigned j = 0, size = p.second.size(); j < size; j++)
            {
              Node t = p.second[j];
              eqc[t] = e;
              eqc_nodes[e].push_back(t);
            }
            eqc_count++;
          }
        }
        eqc_nodes.erase(eqc_curr);
        eqc_curr++;
      }
    }
    // add in already occurring loop variables
    for (std::map<Node, Node>::iterator it = rf.begin(); it != rf.end(); ++it)
    {
      Trace("dt-nconst-debug") << "Mapping equivalence class of " << it->first
                               << " -> " << it->second << std::endl;
      Assert(eqc.find(it->second) != eqc.end());
      eqc[it->first] = eqc[it->second];
    }
    // we now have a partition of equivalent terms
    Trace("dt-nconst") << "Computed equivalence classes ids : " << std::endl;
    for (std::map<Node, int>::iterator it = eqc.begin(); it != eqc.end(); ++it)
    {
      Trace("dt-nconst") << "  " << it->first << " -> " << it->second
                         << std::endl;
    }
    // traverse top-down based on equivalence class
    std::map<int, int> eqc_stack;
    return normalizeCodatatypeConstantEqc(s, eqc_stack, eqc, 0);
  }
  Trace("dt-nconst") << "...invalid." << std::endl;
  return Node::null();
}

// normalize constant : apply to top-level codatatype constants
Node CoDatatypeNormalize::normalizeConstant(Node n)
{
  TypeNode tn = n.getType();
  if (tn.isDatatype())
  {
    if (tn.isCodatatype())
    {
      return normalizeCodatatypeConstant(n);
    }
    else
    {
      std::vector<Node> children;
      bool childrenChanged = false;
      for (unsigned i = 0, size = n.getNumChildren(); i < size; i++)
      {
        Node nc = normalizeConstant(n[i]);
        children.push_back(nc);
        childrenChanged = childrenChanged || nc != n[i];
      }
      if (childrenChanged)
      {
        return NodeManager::currentNM()->mkNode(n.getKind(), children);
      }
    }
  }
  return n;
}

Node CoDatatypeNormalize::collectRef(Node n,
                                     std::vector<Node>& sk,
                                     std::map<Node, Node>& rf,
                                     std::vector<Node>& rf_pending,
                                     std::vector<Node>& terms,
                                     std::map<Node, bool>& cdts)
{
  Assert(n.isConst());
  TypeNode tn = n.getType();
  Node ret = n;
  bool isCdt = false;
  if (tn.isDatatype())
  {
    if (!tn.isCodatatype())
    {
      // nested datatype within codatatype : can be normalized independently
      // since all loops should be self-contained
      ret = normalizeConstant(n);
    }
    else
    {
      isCdt = true;
      if (n.getKind() == kind::APPLY_CONSTRUCTOR)
      {
        sk.push_back(n);
        rf_pending.push_back(Node::null());
        std::vector<Node> children;
        children.push_back(n.getOperator());
        bool childChanged = false;
        for (unsigned i = 0, size = n.getNumChildren(); i < size; i++)
        {
          Node nc = collectRef(n[i], sk, rf, rf_pending, terms, cdts);
          if (nc.isNull())
          {
            return Node::null();
          }
          childChanged = nc != n[i] || childChanged;
          children.push_back(nc);
        }
        sk.pop_back();
        if (childChanged)
        {
          ret = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR,
                                                 children);
          if (!rf_pending.back().isNull())
          {
            rf[rf_pending.back()] = ret;
          }
        }
        else
        {
          Assert(rf_pending.back().isNull());
        }
        rf_pending.pop_back();
      }
      else
      {
        // a loop
        const Integer& i = n.getConst<UninterpretedConstant>().getIndex();
        uint32_t index = i.toUnsignedInt();
        if (index >= sk.size())
        {
          return Node::null();
        }
        Assert(sk.size() == rf_pending.size());
        Node r = rf_pending[rf_pending.size() - 1 - index];
        if (r.isNull())
        {
          r = NodeManager::currentNM()->mkBoundVar(
              sk[rf_pending.size() - 1 - index].getType());
          rf_pending[rf_pending.size() - 1 - index] = r;
        }
        return r;
      }
    }
  }
  Trace("dt-nconst-debug") << "Return term : " << ret << " from " << n
                           << std::endl;
  if (std::find(terms.begin(), terms.end(), ret) == terms.end())
  {
    terms.push_back(ret);
    Assert(ret.getType() == tn);
    cdts[ret] = isCdt;
  }
  return ret;
}
// eqc_stack stores depth
Node CoDatatypeNormalize::normalizeCodatatypeConstantEqc(
    Node n, std::map<int, int>& eqc_stack, std::map<Node, int>& eqc, int depth)
{
  Trace("dt-nconst-debug") << "normalizeCodatatypeConstantEqc: " << n
                           << " depth=" << depth << std::endl;
  if (eqc.find(n) != eqc.end())
  {
    int e = eqc[n];
    std::map<int, int>::iterator it = eqc_stack.find(e);
    if (it != eqc_stack.end())
    {
      int debruijn = depth - it->second - 1;
      return NodeManager::currentNM()->mkConst(
          UninterpretedConstant(n.getType().toType(), debruijn));
    }
    std::vector<Node> children;
    bool childChanged = false;
    eqc_stack[e] = depth;
    for (unsigned i = 0, size = n.getNumChildren(); i < size; i++)
    {
      Node nc = normalizeCodatatypeConstantEqc(n[i], eqc_stack, eqc, depth + 1);
      children.push_back(nc);
      childChanged = childChanged || nc != n[i];
    }
    eqc_stack.erase(e);
    if (childChanged)
    {
      Assert(n.getKind() == kind::APPLY_CONSTRUCTOR);
      children.insert(children.begin(), n.getOperator());
      return NodeManager::currentNM()->mkNode(n.getKind(), children);
    }
  }
  return n;
}

Node CoDatatypeNormalize::replaceDebruijn(Node n,
                                          Node orig,
                                          TypeNode orig_tn,
                                          unsigned depth)
{
  if (n.getKind() == kind::UNINTERPRETED_CONSTANT && n.getType() == orig_tn)
  {
    unsigned index =
        n.getConst<UninterpretedConstant>().getIndex().toUnsignedInt();
    if (index == depth)
    {
      return orig;
    }
  }
  else if (n.getNumChildren() > 0)
  {
    std::vector<Node> children;
    bool childChanged = false;
    for (unsigned i = 0, size = n.getNumChildren(); i < size; i++)
    {
      Node nc = replaceDebruijn(n[i], orig, orig_tn, depth + 1);
      children.push_back(nc);
      childChanged = childChanged || nc != n[i];
    }
    if (childChanged)
    {
      if (n.hasOperator())
      {
        children.insert(children.begin(), n.getOperator());
      }
      return NodeManager::currentNM()->mkNode(n.getKind(), children);
    }
  }
  return n;
}

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4
