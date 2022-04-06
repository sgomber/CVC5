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

#include "theory/builtin/apply_abstract_op.h"
#include "expr/type_node.h"

namespace cvc5::internal {

/**
 */
class AbstractTypeChecker
{
 public:
  /** type check */
  static TypeNode compute(TNode n, bool check);
 private:
  /** Type check */
  static TypeNode computeInternal(const ApplyAbstractOp& aao, const std::vector<TypeNode>& childTypes);
};

}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BUILTIN__APPLY_ABSTRACT_OP_H */
