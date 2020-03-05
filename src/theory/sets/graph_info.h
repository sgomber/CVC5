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
  PathInfo() {}
  /** The atom that corresponds to this path*/
  TNode d_atom;
};

class GraphInfo
{
 public:
  GraphInfo() : d_eidCounter(0) {}
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
  /** Process invalid edge
   *
   * This is called on preregistered atoms that are of the form (c1,c2) in g
   * where (g subset S) but (c1,c2) is not in S.
   */
  void processInvalidEdgeAtom(TNode node);
  /** Get edge info */
  EdgeInfo* getEdgeInfo(TNode src, TNode dst);

  /** The graph variable */
  Node d_var;
  /** The atom corresponding to the subset restriction */
  Node d_subsetAtom;
  /** The set of possible edges (maybe associated with atoms) */
  std::unordered_map<TNode,
                     std::unordered_map<TNode, EdgeInfo, TNodeHashFunction>,
                     TNodeHashFunction>
      d_einfo;
  /** The set of paths that have atoms */
  std::unordered_map<TNode,
                     std::unordered_map<TNode, PathInfo, TNodeHashFunction>,
                     TNodeHashFunction>
      d_pinfo;
  /**
   * Waiting edges, true for edges that have been assigned atoms but have not
   * yet been specified in the subset restriction.
   */
  std::unordered_set<std::pair<TNode, TNode>, TNodePairHashFunction>
      d_einfoWait;
  /** Edge id counter */
  uint32_t d_eidCounter;
};

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SETS__GRAPH_INFO_H */
