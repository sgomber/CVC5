/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for singleton operator for sets.
 */

#include "cvc5_public.h"

#ifndef CVC5__THEORY__BUILTIN__APPLY_ABSTRACT_OP_H
#define CVC5__THEORY__BUILTIN__APPLY_ABSTRACT_OP_H

#include "expr/kind.h"

namespace cvc5::internal {

/**
 */
class ApplyAbstractOp
{
 public:
  ApplyAbstractOp(kind::Kind k);
  ApplyAbstractOp(const ApplyAbstractOp& op);

  /** return the kind of the current object */
  kind::Kind getKind() const;

  bool operator==(const ApplyAbstractOp& op) const;

 private:
  ApplyAbstractOp();
  /** a kind */
  kind::Kind d_kind;
}; /* class ApplyAbstractOp */

std::ostream& operator<<(std::ostream& out, const ApplyAbstractOp& op);

/**
 * Hash function for the ApplyAbstractOp objects.
 */
struct ApplyAbstractOpHashFunction
{
  size_t operator()(const ApplyAbstractOp& op) const;
}; /* struct ApplyAbstractOpHashFunction */

}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BUILTIN__APPLY_ABSTRACT_OP_H */
