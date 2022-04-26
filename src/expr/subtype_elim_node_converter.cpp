/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of subtype elimination node conversion
 */

#include "expr/subtype_elim_node_converter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

SubtypeElimNodeConverter::SubtypeElimNodeConverter() {}

bool SubtypeElimNodeConverter::isRealTypeStrict(TypeNode tn)
{
  return tn.isReal() && !tn.isInteger();
}

Node SubtypeElimNodeConverter::postConvert(Node n)
{
  return n;
}

}  // namespace cvc5::internal
