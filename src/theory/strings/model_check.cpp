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
  Trace("strings-mc") << "ModelCheck::check..." << std::endl;
  Trace("strings-mc") << "Model M {" << std::endl;
  std::vector<Node> vars;
  std::vector<Node> subs;
  for (const std::pair<const Node, Node>& meq : model)
  {
    if (meq.first != meq.second)
    {
      vars.push_back(meq.first);
      subs.push_back(meq.second);
      Trace("strings-mc") << "  M(" << meq.first << ") = " << meq.second
                          << std::endl;
    }
  }
  Trace("strings-mc") << "}" << std::endl;
  Trace("strings-mc") << "Assertions:" << std::endl;
  for (Theory::assertions_iterator it = d_parent.facts_begin(),
                                   itEnd = d_parent.facts_end();
       it != itEnd;
       ++it)
  {
    Node lit = (*it).d_assertion;
    Trace("strings-mc") << "- " << lit << std::endl;
    // evaluate it
    Node litEval = d_eval.eval(lit, vars, subs);
    Trace("strings-mc") << "- eval: " << litEval << std::endl;
  }
  exit(1);
  return false;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
