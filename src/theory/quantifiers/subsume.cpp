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

void Subsume::setSubsumes(Node q, Node qsubsumed)
{
  d_subsumes[q].push_back(qsubsumed);
  d_subsumes[qsubsumed].push_back(q);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
