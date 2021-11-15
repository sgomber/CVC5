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
#include "theory/quantifiers/term_database.h"

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
      d_watchEqcList(c),
      d_watchEqcIndex(0)
{
}

void PatTermInfo::initialize(TNode pattern, TermDb* tdb)
{
  Assert(expr::hasFreeVar(pattern));
  d_pattern = pattern;
  d_isBooleanConnective = expr::isBooleanConnective(pattern);
  if (!d_isBooleanConnective)
  {
    d_matchOp = tdb->getMatchOperator(pattern);
  }
}

void PatTermInfo::resetRound()
{
  Assert (d_watchEqc.empty());
  Assert (d_watchEqcList.empty());
  d_watchEqcIndex = 0;
  Assert (isActive());
  if (d_isBooleanConnective)
  {
    /*
    for (TNode pc : pattern)
    {
      if (!expr::hasFreeVar(pc))
      {
        continue;
      }
      d_numUnassigned = d_numUnassigned + 1;
    }
    */
    // TODO: duplicate children?? should probably handle in rewriter
    // for quantifiers
    d_numUnassigned = d_pattern.getNumChildren();
  }
}

bool PatTermInfo::isActive() const { return d_eq.get().isNull(); }

void PatTermInfo::addWatchEqc(TNode eqc)
{
  if (d_watchEqc.find(eqc)==d_watchEqc.end())
  {
    d_watchEqc.insert(eqc);
    d_watchEqcList.push_back(eqc);
  }
}

TNode PatTermInfo::getNextWatchEqc()
{
  if (d_watchEqcIndex >= d_watchEqcList.size())
  {
    return TNode::null();
  }
  TNode next = d_watchEqcList[d_watchEqcIndex];
  d_watchEqcIndex = d_watchEqcIndex.get() + 1;
  return next;
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
