/*********************                                                        */
/*! \file model_check.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of a model check module for strings
 **/

#include "theory/strings/model_check.h"

#include "theory/strings/theory_strings.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

ModelCheck::ModelCheck(TheoryStrings& parent) : d_parent(parent) {}

ModelCheck::~ModelCheck() {}

bool ModelCheck::check(const std::map<Node, Node>& model)
{
  std::vector<Node> assertions;
  for (Theory::assertions_iterator it = d_parent.facts_begin(),
                                   itEnd = d_parent.facts_end();
       it != itEnd;
       ++it)
  {
    assertions.insert(it->d_assertion);
  }
  return false;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
