/*********************                                                        */
/*! \file node_type_set.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A set of nodes that are partitioned by type
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__NODE_TYPE_SET_H
#define CVC4__EXPR__NODE_TYPE_SET_H

#include <vector>
#include <unordered_set>

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {

/**
 * A set of terms that also partitions the nodes per type.
 */
class NodeTypeSet 
{
public:
  NodeTypeSet(){}
  virtual ~NodeTypeSet(){}
  /** Add n to this set. */
  void add(TNode n);
  /** Clear this set */
  void clear();
  /** Does this set contain n? */
  bool contains(TNode n);
  /** Get all nodes */
  const std::unordered_set<Node, NodeHashFunction>& get() const;
  /** Get all nodes of type tn */
  const std::vector<Node>& getForType(TypeNode tn) const;
protected:
  /** All terms */
  std::unordered_set<Node, NodeHashFunction> d_nodes;
  /** All terms per type */
  std::map<TypeNode, std::vector<Node> > d_nodeTypes;
  /** Empty vector */
  std::vector<Node> d_emptyVec;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__NODE_TYPE_SET_H */
