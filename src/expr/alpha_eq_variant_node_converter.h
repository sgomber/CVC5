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
#include "proof/eager_proof_generator.h"

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

 private:
  /** Mapping bound variables to fresh bound variables of the same type */
  std::map<Node, Node> d_bvMap;
};

/**
 * Proof-producing version of the above class. Stores
 */
class AlphaEqVariantProofGenerator : public EagerProofGenerator
{
 public:
  AlphaEqVariantProofGenerator(
      ProofNodeManager* pnm,
      context::Context* c = nullptr,
      std::string name = "AlphaEqVariantProofGenerator");
  /** Convert trust node */
  TrustNode convertEq(TrustNode eqt);
};

}  // namespace cvc5

#endif
