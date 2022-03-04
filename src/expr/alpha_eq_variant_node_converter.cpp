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
 * Implementation of subtype elimination node conversion
 */

#include "expr/alpha_eq_variant_node_converter.h"

using namespace cvc5::kind;

namespace cvc5 {

AlphaEqVariantNodeConverter::AlphaEqVariantNodeConverter() {}

Node AlphaEqVariantNodeConverter::postConvert(Node n)
{
  if (n.getKind() == BOUND_VARIABLE)
  {
    std::map<Node, Node>::iterator it = d_bvMap.find(n);
    if (it != d_bvMap.end())
    {
      return it->second;
    }
    Node v = NodeManager::currentNM()->mkBoundVar(n.getType());
    d_bvMap[n] = v;
    return v;
  }
  return n;
}

AlphaEqVariantProofGenerator::AlphaEqVariantProofGenerator(
    ProofNodeManager* pnm, context::Context* c, std::string name)
    : EagerProofGenerator(pnm, c, name)
{
}

TrustNode AlphaEqVariantProofGenerator::convertEq(TrustNode eqt) { return eqt; }

}  // namespace cvc5
