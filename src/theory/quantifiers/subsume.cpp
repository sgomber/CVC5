/*********************                                                        */
/*! \file subsume.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Subsume
 **
 **/

#include "theory/quantifiers/subsume.h"

using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Subsume::Subsume(QuantifiersEngine* qe) {}

bool Subsume::empty() const { return d_subsumes.empty(); }

void Subsume::setSubsumes(Node q, Node qsubsumed)
{
  d_subsumes[q].push_back(qsubsumed);
  d_subsumed_by[qsubsumed].push_back(q);
}

bool Subsume::getSubsumes(Node q,
                          std::map<Node, std::vector<Node> >::iterator& it)
{
  it = d_subsumes.find(q);
  return it != d_subsumes.end();
}

bool Subsume::getSubsumedBy(Node q,
                            std::map<Node, std::vector<Node> >::iterator& it)
{
  it = d_subsumed_by.find(q);
  return it != d_subsumed_by.end();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
