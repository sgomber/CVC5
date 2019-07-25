/*********************                                                        */
/*! \file proof_db_pf.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof data structure Proof db.
 **/

#include "theory/proof_db_pf.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
  
void ProofDbRule::init(const std::string& name, const std::vector<Node>& cond, Node eq)
{
  d_name = name;
  d_cond.clear();
  d_cond.insert(d_cond.end(),cond.begin(),cond.end());
  d_eq = eq;
}

}  // namespace theory
}  // namespace CVC4
