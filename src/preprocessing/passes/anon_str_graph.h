/*********************                                                        */
/*! \file anon_str_graph.h
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

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__ANON_STR_GRAPH_H
#define __CVC4__PREPROCESSING__PASSES__ANON_STR_GRAPH_H

#include <unordered_map>
#include <unordered_set>
#include "expr/node.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class Graph;

class CtnNode
{
 public:
  Node d_this;
  /** 0:children, 1:parents */
  std::unordered_set<Node, NodeHashFunction> d_edges[2];

  void getTransitiveClosure(Graph& graph,
                            std::unordered_set<Node, NodeHashFunction>& t,
                            unsigned dir);
  void debugPrint(const char* c) const;

  void removeEdge(Graph& graph, Node c, unsigned dir);
};

class Graph
{
 public:
  std::map<Node, CtnNode> d_graph;
  std::unordered_set<Node, NodeHashFunction> d_baseNodes[2];

  void build(const std::vector<Node>& litSet);
  void build(const std::vector<Node>& litSet,
             const std::map<Node, Node>& valMap);
  void add(Node l);
  void add(Node l, const std::map<Node, Node>& valMap);

 private:
  static std::map<Node, Node> d_emptyMap;
  void addInternal(Node l,
                   CtnNode& cl,
                   unsigned dir,
                   std::unordered_set<Node, NodeHashFunction>& processed,
                   std::unordered_set<Node, NodeHashFunction>& transCtn,
                   const std::map<Node, Node>& valMap);
};
}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__ANON_STR_GRAPH_H */
