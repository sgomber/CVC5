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
 * Info per free variable in CCFV.
 */

#include "theory/quantifiers/ccfv/free_var_info.h"

#include "theory/quantifiers/ccfv/state.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ccfv {

FreeVarInfo::FreeVarInfo(context::Context* c)
    : d_finalTerms(c), d_quantList(c), d_quantIndex(c, 0)
{
}

TNode FreeVarInfo::getNextQuantifier()
{
  if (d_quantIndex >= d_quantList.size())
  {
    return TNode::null();
  }
  TNode next = d_quantList[d_quantIndex];
  d_quantIndex = d_quantIndex.get() + 1;
  return next;
}

void FreeVarInfo::resetLevel() { d_quantIndex = 0; }

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
