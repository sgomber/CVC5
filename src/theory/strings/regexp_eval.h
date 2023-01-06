/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Evaluator for regular expression membership.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__REGEXP_EVAL_H
#define CVC5__THEORY__STRINGS__REGEXP_EVAL_H

#include "expr/node.h"
#include "util/string.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

class RegExpEval
{
 public:
  static bool canEvaluate(const Node& r);
  static bool evaluate(String& s, const Node& r);
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__REWRITES_H */
