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
 * Set of quantified formulas
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__QUANT_SET_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__QUANT_SET_H

#include <vector>

#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

class QuantifiersSet
{
 public:
  QuantifiersSet() {}
  /** the list of quantified formulas */
  std::vector<TNode> d_quants;
  /** The index of the quantified formula we are assigning the variables of */
  size_t d_qindex;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
