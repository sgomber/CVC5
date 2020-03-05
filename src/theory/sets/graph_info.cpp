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
  Assert(node.getKind()==SUBSET);
  Assert(d_var==node[0]);
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
        Trace("graph-info") << "Edge: (" << cur[0][0] << ", " << cur[0][1]
                            << ") ?in " << d_var << std::endl;
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
}

void GraphInfo::addEdgeAtom(TNode node, bool isPath)
{
  
}
  
void GraphInfo::addEdge(TNode src, TNode dst)
{
  Assert(src.isConst());
  Assert(dst.isConst());
  EdgeInfo& ei = d_einfo[src][dst];
  if (ei.d_id == 0)
  {
    d_idCounter++;
    ei.d_id = d_idCounter;
  }
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
