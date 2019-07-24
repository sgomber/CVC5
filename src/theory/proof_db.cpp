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

bool ProofDb::existsRule( Node a, Node b, unsigned& index )
{
  if( a==b )
  {
    // reflexivity
    return true;
  }
  if( b.isConst() )
  {
    // nullary symbols should not rewrite to constants
    Assert( a.getNumChildren()!=0 );
    bool allConst = true;
    for( const Node& ac : a )
    {
      if( !ac.isConst() )
      {
        allConst = false;
      }
    }
    if( allConst )
    {
      // evaluation
      return true;
    }
  }
  Kind ak = a.getKind();
  Kind bk = b.getKind();
  if( ak==EQUAL && bk==EQUAL )
  {
    if( a[0]==b[1] && b[0]==a[1] )
    {
      // symmetry of equality 
      return true;
    }
  }
  return false;
}

bool ProofDb::existsRule( Node a, Node b)
{
  unsigned index = 0;
  return existsRule(a,b,index);
}

bool ProofDb::proveRule( Node a, Node b )
{
  return false;
}

void ProofDb::notify( Node a, Node b)
{
  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
  notify(a,b,*nodeManagerOptions.getOut());
}
void ProofDb::notify( Node a, Node b, std::ostream& out )
{
  if( existsRule(a,b) )
  {
    // already exists
    return;
  }
  out << "(trusted (= " << a << " " << b << "))" << std::endl;
}

}  // namespace theory
}  // namespace CVC4
