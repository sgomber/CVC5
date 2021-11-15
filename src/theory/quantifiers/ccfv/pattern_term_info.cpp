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
    : d_eq(c),
      d_numUnassigned(c, 0),
      d_parentNotify(c),
      d_parentCongNotify(c),
      d_watchEqc(c),
      d_watchEqcIndex(0)
{
}

void PatTermInfo::initialize(TNode pattern)
{
  Assert(expr::hasFreeVar(pattern));
  d_pattern = pattern;
  d_isBooleanConnective = expr::isBooleanConnective(pattern);
  if (d_isBooleanConnective)
  {
    for (TNode pc : pattern)
    {
      if (expr::hasFreeVar(pc))
      {
        d_numUnassigned = d_numUnassigned + 1;
      }
    }
  }
  Assert(d_eq.get().isNull());
}

bool PatTermInfo::isActive() const { return d_eq.get().isNull(); }

Node PatTermInfo::getNextWatchEqc()
{
  if (d_watchEqcIndex >= d_watchEqc.size())
  {
    return TNode::null();
  }
  TNode next = d_watchEqc[d_watchEqcIndex];
  d_watchEqcIndex = d_watchEqcIndex.get() + 1;
  return next;
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
