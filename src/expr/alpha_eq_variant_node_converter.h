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
 * Implementation of alpha equivalent variant node conversion
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__EXPR__ALPHA_EQ_VARIANT_NODE_CONVERTER_H
#define CVC4__PROOF__EXPR__ALPHA_EQ_VARIANT_NODE_CONVERTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "expr/type_node.h"
#include "proof/lazy_proof.h"

namespace cvc5 {

/**
 * This converts a node into an alpha equivalent node whose occurrences of
 * BOUND_VARIABLE are fresh.
 */
class AlphaEqVariantNodeConverter : public NodeConverter
{
 public:
  AlphaEqVariantNodeConverter();
  ~AlphaEqVariantNodeConverter() {}
  /** convert node n as described above during post-order traversal */
  Node postConvert(Node n) override;
  /** get mapping */
  const std::map<Node, Node>& getVariableMapping() const;

 private:
  /** Mapping bound variables to fresh bound variables of the same type */
  std::map<Node, Node> d_bvMap;
};

/**
 * Proof-producing version of the above class. Stores
 */
class AlphaEqVariantProofGenerator : public ProofGenerator
{
 public:
  AlphaEqVariantProofGenerator(
      ProofNodeManager* pnm,
      context::Context* c = nullptr,
      const std::string& name = "AlphaEqVariantProofGenerator");
  /** Get the proof for formula f. */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /**
   * Convert node to be an alpha equivalent variant. This:
   * - Returns the converted form n' of n based on the node converter above,
   * - Ensures that this proof generator can provide a proof of (= n n').
   */
  Node convert(Node n);
  /**
   * Assume that pg (if non-null) has a proof of (= lhs rhs). This updates
   * rhs to its converted form rhs' using the convert method of this class,
   * then returns a proof generator that has a proof of (= lhs rhs'), which
   * may be pg if rhs == rhs', or this class otherwise. It may return nullptr
   * if pg is nullptr.
   */
  ProofGenerator* convertEq(Node lhs, Node& rhs, ProofGenerator* pg);
  /** Identify this generator (for debugging, etc..) */
  std::string identify() const override;

 private:
  /**
   * A lazy cd proof for storing intermediate steps for implementing the above
   * methods.
   */
  std::unique_ptr<LazyCDProof> d_proof;
  /** name */
  std::string d_name;
};

}  // namespace cvc5

#endif
