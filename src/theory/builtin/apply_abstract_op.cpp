/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Mathias Preiner
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

#include "theory/sets/singleton_op.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const ApplyAbstractOp& op)
{
  return out << "(ApplyAbstractOp " << op.getKind() << ')';
}

size_t ApplyAbstractOpHashFunction::operator()(const ApplyAbstractOp& op) const
{
  return kind::KindHashFunction(op.getKind());
}

ApplyAbstractOp::ApplyAbstractOp(kind::Kind k)
    : d_kind(k)
{
}

ApplyAbstractOp::ApplyAbstractOp(const ApplyAbstractOp& op)
    : d_kind(op.getKind())
{
}

Kind ApplyAbstractOp::getKind() const { return d_kind; }

bool ApplyAbstractOp::operator==(const ApplyAbstractOp& op) const
{
  return getKind() == op.getKind();
}

}  // namespace cvc5::internal
