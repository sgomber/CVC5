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

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

void GraphInfo::addEdge(TNode src, TNode dst)
{
  EdgeInfo& ei = d_einfo[src][dst];
  if (ei.d_id == 0)
  {
    d_idCounter++;
    ei.d_id = d_idCounter;
  }
}

}  // namespace sets
}  // namespace theory
}  // namespace CVC4
