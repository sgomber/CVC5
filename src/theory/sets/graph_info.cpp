/*********************                                                        */
/*! \file graph_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of data structures for the graph extension.
 **/

#include "theory/sets/graph_info.h"

#include "smt/logic_exception.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

void GraphInfo::initialize(TNode g)
{
  if (!g.isVar())
  {
    std::stringstream ss;
    ss << "GraphInfo: Cannot handle graph that is not a variable: " << g;
    throw LogicException(ss.str());
  }
  Assert(d_var.isNull());
  d_var = g;
}

void GraphInfo::addSubsetRestriction(TNode node)
{
  Assert(node.getKind() == SUBSET);
  Assert(d_var == node[0]);
  if (!d_subsetAtom.isNull())
  {
    std::stringstream ss;
    ss << "GraphInfo: Cannot handle multiple subset restrictions for graph "
       << d_var;
    throw LogicException(ss.str());
  }
  d_subsetAtom = node;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(node[1]);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.getKind() == UNION)
      {
        for (TNode cn : cur)
        {
          visit.push_back(cn);
        }
      }
      else if (cur.getKind() == SINGLETON)
      {
        // cur[0] should be a constant tuple (c1, c2).
        checkEdge(cur[0]);
        addEdge(cur[0][0], cur[0][1]);
      }
      else
      {
        std::stringstream ss;
        ss << "GraphExtension: Cannot handle non-constant in subset "
              "restriction for graph: "
           << cur;
        throw LogicException(ss.str());
      }
    }
  } while (!visit.empty());

  // process any edge still on the waitlist
  for (const std::pair<TNode, TNode>& w : d_einfoWait)
  {
    TNode src = w.first;
    TNode dst = w.second;
    std::unordered_map<TNode, EdgeInfo, TNodeHashFunction>& srcEdges =
        d_einfo[src];
    EdgeInfo& ei = srcEdges[dst];
    processInvalidEdgeAtom(ei.d_atom);
    // remove the edge info
    srcEdges.erase(dst);
  }
  d_einfoWait.clear();
}

void GraphInfo::addEdgeAtom(TNode node, bool isPath)
{
  checkEdge(node[0]);
  TNode src = node[0][0];
  TNode dst = node[0][1];
  if (isPath)
  {
    PathInfo& pi = d_pinfo[src][dst];
    pi.d_atom = node;
    Trace("graph-info") << "- Path: (" << src << ", " << dst << ") ?in "
                        << d_var << ", atom: " << node << std::endl;
    return;
  }
  if (d_subsetAtom.isNull())
  {
    // set the atom
    EdgeInfo& ei = d_einfo[src][dst];
    ei.d_atom = node;
    // add to waiting list
    d_einfoWait.insert(std::pair<TNode, TNode>(src, dst));
    return;
  }
  // otherwise lookup the edge info
  EdgeInfo* ei = getEdgeInfo(src, dst);
  if (ei == nullptr)
  {
    // If we've assigned the restriction already, then this edge should be
    // in the set of possible edges. If not, we are in this case; the atom is
    // trivially false.
    processInvalidEdgeAtom(node);
    return;
  }
  // set the atom
  ei->d_atom = node;
}

void GraphInfo::processInvalidEdgeAtom(TNode node)
{
  Assert(!node.isNull());
  Trace("graph-info") << "- Edge (INVALID): " << node << std::endl;
  // TODO?
}

void GraphInfo::addEdge(TNode src, TNode dst)
{
  Assert(src.isConst());
  Assert(dst.isConst());
  EdgeInfo& ei = d_einfo[src][dst];
  if (ei.d_id == 0)
  {
    d_eidCounter++;
    ei.d_id = d_eidCounter;
  }
  Trace("graph-info") << "- Edge: (" << src << ", " << dst << ") ?in " << d_var;
  // if it has an atom, remove from waiting list
  if (!ei.d_atom.isNull())
  {
    Trace("graph-info") << ", atom: " << ei.d_atom;
    // remove from waitlist
    std::pair<TNode, TNode> p = std::pair<TNode, TNode>(src, dst);
    Assert(d_einfoWait.find(p) != d_einfoWait.end());
    d_einfoWait.erase(p);
  }
  Trace("graph-info") << std::endl;
}

EdgeInfo* GraphInfo::getEdgeInfo(TNode src, TNode dst)
{
  std::unordered_map<TNode,
                     std::unordered_map<TNode, EdgeInfo, TNodeHashFunction>,
                     TNodeHashFunction>::iterator it = d_einfo.find(src);
  if (it == d_einfo.end())
  {
    return nullptr;
  }
  std::unordered_map<TNode, EdgeInfo, TNodeHashFunction>::iterator it2 =
      it->second.find(dst);
  if (it2 == it->second.end())
  {
    return nullptr;
  }
  return &it2->second;
}

void GraphInfo::checkEdge(TNode c)
{
  if (c.getKind() != APPLY_CONSTRUCTOR || c.getNumChildren() != 2
      || !c[0].isConst() || !c[1].isConst())
  {
    std::stringstream ss;
    ss << "GraphExtension: Cannot handle non-constant edge " << c;
    throw LogicException(ss.str());
  }
}

}  // namespace sets
}  // namespace theory
}  // namespace CVC4
