/*********************                                                        */
/*! \file anonymize_strings.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The rewrite preprocessing pass
 **
 ** Calls the rewriter on every assertion
 **/

#include "preprocessing/passes/anon_str_graph.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;


void CtnNode::getTransitiveClosure(Graph& graph,
                          std::unordered_set<Node, NodeHashFunction>& t,
                          unsigned dir)
{
  if (t.find(d_this) != t.end())
  {
    // already processed
    return;
  }
  t.insert(d_this);
  for (const Node& c : d_edges[dir])
  {
    Assert(graph.d_graph.find(c) != graph.d_graph.end());
    graph.d_graph[c].getTransitiveClosure(graph, t, dir);
  }
}
void CtnNode::debugPrint(const char* c) const
{
  Trace(c) << "Node(" << d_this << "):" << std::endl;
  for (unsigned dir = 0; dir <= 1; dir++)
  {
    Trace(c) << "  " << (dir == 0 ? "children:" : "parent:") << " ";
    for (const Node& e : d_edges[dir])
    {
      Trace(c) << e << " ";
    }
    Trace(c) << std::endl;
  }
}

void CtnNode::removeEdge(Graph& graph, Node c, unsigned dir)
{
  Assert(d_edges[dir].find(c) != d_edges[dir].end());
  d_edges[dir].erase(c);
  Assert(graph.d_graph.find(c) != graph.d_graph.end());
  CtnNode& cc = graph.d_graph[c];
  Assert(cc.d_edges[1 - dir].find(d_this) != cc.d_edges[1 - dir].end());
  cc.d_edges[1 - dir].erase(d_this);
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
