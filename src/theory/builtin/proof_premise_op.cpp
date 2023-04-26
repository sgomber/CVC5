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

#include "theory/builtin/proof_premise_op.h"

#include <iostream>
#include <sstream>
#include "expr/node.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const ProofPremiseOp& op)
{
  return out << "(proves " << op.getProven().toString() << ')';
}

size_t ProofPremiseOpHashFunction::operator()(const ProofPremiseOp& op) const
{
  return std::hash<Node>()(op.getProven());
}

ProofPremiseOp::ProofPremiseOp(const Node& p) : d_proven(new Node(p)) {}

ProofPremiseOp::ProofPremiseOp(const ProofPremiseOp& op) : d_proven(new Node(op.getProven())) {}

const Node& ProofPremiseOp::getProven() const { return *d_proven; }

bool ProofPremiseOp::operator==(const ProofPremiseOp& op) const
{
  return getProven() == op.getProven();
}

}  // namespace cvc5::internal
