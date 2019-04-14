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

void Subsume::reset_round()
{
  d_curr_subumed_by.clear();
  Trace("subsume-debug") << "Subsume::reset_round" << std::endl;
}

bool Subsume::computeCurrentSubsumedBy( Node q, std::map< Node, bool >& qassert )
{
  // should not have computed already
  Assert( d_curr_subumed_by.find(q)==d_curr_subumed_by.end() );
  std::map<Node, std::vector<Node> >::iterator its = d_subsumed_by.find(q);
  if( its!=d_subsumed_by.end() )
  {
    // check whether any quantified formula that subsumes it is currently
    // asserted
    for (const Node& sq : its->second)
    {
      if (qassert.find(sq) != qassert.end())
      {
        Trace("subsume-debug") << "* " << q << " subsumed by " << sq << std::endl;
        // store it
        d_curr_subumed_by[q] = sq;
        return true;
      }
    }
  }
  return false;
}

Node Subsume::getCurrentlySubsumedBy( Node q ) const
{
  std::map< Node, Node >::const_iterator it = d_curr_subumed_by.find(q);
  if( it!=d_curr_subumed_by.end() )
  {
    return it->second;
  }
  return Node::null();
}
  
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
