/*********************                                                        */
/*! \file proof_db.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of Proof db.
 **/

#include "theory/proof_db.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

void ProofDb::registerRules(const std::map< Node, std::string >& rules)
{
  // TODO
  for( const std::pair< const Node, std::string >& rr : rules )
  {
    Node r = rr.first;
    AlwaysAssert( r.getKind()==IMPLIES );
    
    // add to discrimination tree
  }
}

bool ProofDb::existsRule( Node eq, unsigned& index )
{
  return false;
}

bool ProofDb::proveRule( Node eq )
{
  return false;
}

bool ProofDb::notify( Node a, Node b )
{
 
  
}

}  // namespace theory
}  // namespace CVC4
