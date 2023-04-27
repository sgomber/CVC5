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
 * A class for representing proof premises
 */

#include "theory/builtin/proven_op.h"

#include <iostream>
#include <sstream>

#include "expr/node.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const ProvenOp& op)
{
  return out << "(proven_op " << op.getProven().getId() << ')';
}

size_t ProvenOpHashFunction::operator()(const ProvenOp& op) const
{
  return std::hash<Node>()(op.getProven());
}

ProvenOp::ProvenOp(const Node& p) : d_proven(new Node(p)) {}

ProvenOp::ProvenOp(const ProvenOp& op)
    : d_proven(new Node(op.getProven()))
{
}

const Node& ProvenOp::getProven() const { return *d_proven; }

bool ProvenOp::operator==(const ProvenOp& op) const
{
  return getProven() == op.getProven();
}

}  // namespace cvc5::internal
