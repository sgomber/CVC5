/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Information for each search level in ccfv
 */

#include "theory/quantifiers/ccfv/search_level.h"

#include <sstream>

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ccfv {

SearchLevel::SearchLevel() : d_firstTimePre(true), d_firstTimePost(true) {}

std::string SearchLevel::toStringDebug() const
{
  std::stringstream ss;
  ss << "Variables: " << d_varsToAssign << std::endl;
  for (size_t i = 0; i < 2; i++)
  {
    const std::vector<TNode>& quants = i == 0 ? d_startQuants : d_finalQuants;
    ss << (i == 0 ? "Start" : "Final") << " quants: [ ";
    for (TNode q : quants)
    {
      ss << q.getId() << " ";
    }
    ss << "]" << std::endl;
  }
  return ss.str();
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
