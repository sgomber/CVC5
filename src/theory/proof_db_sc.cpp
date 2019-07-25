/*********************                                                        */
/*! \file proof_db_sc.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof side conditions
 **/

#include "theory/proof_db_sc.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
  
Node ProofDbSideCondition::evaluate(Node n)
{
  return Node::null();
}

Node ProofDbSideCondition::run(const std::string& fname, std::vector< Node >& args )
{
  return Node::null();
}

Node ProofDbSideCondition::flatten(Node n)
{
  return Node::null();
}

Node ProofDbSideCondition::flatten2(Node op, Node n, Node nacc)
{
  return Node::null();
}

}  // namespace theory
}  // namespace CVC4
