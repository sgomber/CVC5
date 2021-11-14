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
 * Info per pattern term in CCFV.
 */

#include "theory/quantifiers/ccfv/pattern_term_info.h"

#include "expr/node_algorithm.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

PatTermInfo::PatTermInfo(context::Context* c)
    : d_eq(c), d_numUnassignChildren(c, 0)
{
}

void PatTermInfo::initialize(TNode pattern)
{
  Assert(expr::hasFreeVar(pattern));
  d_pattern = pattern;
  for (TNode pc : pattern)
  {
    if (expr::hasFreeVar(pc))
    {
      d_numUnassignChildren = d_numUnassignChildren + 1;
    }
  }
  Assert(d_eq.isNull());
}

bool PatTermInfo::isActive() const { return d_eq.get().isNull(); }

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
