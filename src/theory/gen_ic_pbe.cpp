/*********************                                                        */
/*! \file gen_ic_pbe.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of gen_ic_pbe
 **/

#include "theory/gen_ic_pbe.h"

#include "theory/quantifiers/sygus_sampler.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
  
GenIcPbe::GenIcPbe() {

}

void GenIcPbe::run()
{
  NodeManager * nm = NodeManager::currentNM();

  TypeNode ftt = nm->mkFloatingPointType(4,5);
  Node s = nm->mkBoundVar("s", ftt);
  Node t = nm->mkBoundVar("t", ftt);
  Node x = nm->mkBoundVar("x", ftt);
  
  std::vector< Node > vars;
  vars.push_back(s);
  vars.push_back(t);
  
  //Node icCase = nm->mkNode( EQUAL, nm->mkNode( FP
  
  
}

} /* CVC4::theory namespace */
} /* CVC4 namespace */
