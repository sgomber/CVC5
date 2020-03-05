/*********************                                                        */
/*! \file graph_extension.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of an extension of the sets theory that specializes in
 ** finite graphs.
 **/

#include "theory/sets/graph_extension.h"

#include "expr/datatype.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

GraphExtension::GraphExtension(SolverState& s,
                               InferenceManager& im,
                               eq::EqualityEngine& e,
                               context::Context* c,
                               context::UserContext* u)
    : d_state(s), d_im(im), d_ee(e)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

GraphExtension::~GraphExtension() {}

void GraphExtension::preRegisterTerm(TNode node)
{
  
}
 
void GraphExtension::assertNode(TNode lit)
{
  
}
 
void GraphExtension::check(Theory::Effort level)
{

}

}
}
}
