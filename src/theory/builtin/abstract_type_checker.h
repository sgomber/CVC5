/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements the type checker for APPLY_ABSTRACT
 */

#include "cvc5_public.h"

#ifndef CVC5__THEORY__BUILTIN__ABSTRACT_TYPE_CHECKER_H
#define CVC5__THEORY__BUILTIN__ABSTRACT_TYPE_CHECKER_H

#include "expr/type_node.h"
#include "theory/builtin/apply_abstract_op.h"

namespace cvc5::internal {

/**
 */
class AbstractTypeChecker
{
 public:
  /** type check */
  static TypeNode compute(TNode n, bool check);

  /**
   * Type check the type of
   *   (APPLY_ABSTRACT (APPLY_ABSTRACT_OP k) children)
   * Return the null type node if it does not type check.
   */
  static TypeNode computeAbstractApp(Kind k,
                                     const std::vector<Node>& children,
                                     bool check);
};

}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BUILTIN__APPLY_ABSTRACT_OP_H */
