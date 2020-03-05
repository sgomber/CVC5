/*********************                                                        */
/*! \file graph_info.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Data structures for the graph extension
 **/

#ifndef CVC4__THEORY__SETS__GRAPH_INFO_H
#define CVC4__THEORY__SETS__GRAPH_INFO_H

#include <unordered_map>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace sets {

class EdgeInfo
{
 public:
  EdgeInfo() : d_id(0) {}
  /** Edge Id */
  uint32_t d_id;
  /** The atom that corresponds to this edge (if one exists) */
  TNode d_atom;
};

class PathInfo
{
 public:
  PathInfo() : d_id(0) {}
  /** Path Id */
  uint32_t d_id;
};

class GraphInfo
{
 public:
  GraphInfo() : d_idCounter(0) {}
  /** initialize */
  void initialize(TNode g);
  /** add subset restriction */
  void addSubsetRestriction(TNode node);
  /** add edge atom */
  void addEdgeAtom(TNode node, bool isPath = false);

 private:
  //------------------------------------- logic checks
  /** Logic exception if g is not a graph (binary relation) variable */
  void checkGraphVariable(TNode g);
  /** Logic exception if t is not a constant tuple (c1,c2) */
  void checkEdge(TNode c);
  //------------------------------------- end logic checks
  /** Add edge */
  void addEdge(TNode src, TNode dst);

  /** The graph variable */
  Node d_var;
  /** The atom corresponding to the subset restriction */
  Node d_subsetAtom;
  /** The domain of possible edges */
  std::unordered_map<TNode,
                     std::unordered_map<TNode, EdgeInfo, TNodeHashFunction>,
                     TNodeHashFunction>
      d_einfo;
  /** Id counter */
  uint32_t d_idCounter;
};

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SETS__GRAPH_INFO_H */
