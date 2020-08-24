/*********************                                                        */
/*! \file node_type_set.cpp
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

#include "expr/node_type_set.h"

namespace CVC4 {

void NodeTypeSet::add(TNode n)
{
  if (d_nodes.find(n)!=d_nodes.end())
  {
    return;
  }
  d_nodes.insert(n);
  d_nodeTypes[n.getType()].push_back(n);
}

void NodeTypeSet::clear()
{
  d_nodes.clear();
  d_nodeTypes.clear();
}

bool NodeTypeSet::contains(TNode n)
{
  return d_nodes.find(n)!=d_nodes.end();
}

const std::unordered_set<Node, NodeHashFunction>& NodeTypeSet::get() const
{
  return d_nodes;
}

const std::vector<Node>& NodeTypeSet::getForType(TypeNode tn) const
{
  std::map<TypeNode, std::vector<Node> >::const_iterator it =
      d_nodeTypes.find(tn);
  if (it != d_nodeTypes.end())
  {
    return it->second;
  }
  // otherwise just return the empty vector
  return d_emptyVec;
}

}  // namespace CVC4
