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

#include "cvc5_public.h"

#ifndef CVC5__THEORY__BUILTIN__PROOF_PREMISE_OP_H
#define CVC5__THEORY__BUILTIN__PROOF_PREMISE_OP_H

#include <memory>
#include <vector>

namespace cvc5::internal {

template <bool ref_count>
class NodeTemplate;
typedef NodeTemplate<true> Node;

/**
 * The payload for proof premises, payload is a formula that is proven.
 */
class ProofPremiseOp
{
 public:
  ProofPremiseOp(const Node& p);
  ProofPremiseOp(const ProofPremiseOp& op);

  /** Return the kind of indexed operator this operator represents */
  const Node& getProven() const;

  bool operator==(const ProofPremiseOp& op) const;

 private:
  ProofPremiseOp();
  /** The kind of indexed operator this operator represents */
  std::unique_ptr<Node> d_proven;
};

std::ostream& operator<<(std::ostream& out, const ProofPremiseOp& op);

/**
 * Hash function for the ProofPremiseOp objects.
 */
struct ProofPremiseOpHashFunction
{
  size_t operator()(const ProofPremiseOp& op) const;
};

}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BUILTIN__PROOF_PREMISE_OP_H */
