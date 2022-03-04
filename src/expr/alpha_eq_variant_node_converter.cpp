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

const std::map<Node, Node>& AlphaEqVariantNodeConverter::getVariableMapping()
    const
{
  return d_bvMap;
}

AlphaEqVariantProofGenerator::AlphaEqVariantProofGenerator(
    ProofNodeManager* pnm, context::Context* c, const std::string& name)
    : ProofGenerator(),
      d_proof(pnm, nullptr, c, name + "::LazyCDProof", false),
      d_name(name)
{
}
std::shared_ptr<ProofNode> AlphaEqVariantProofGenerator::getProofFor(Node f)
{
  return d_proof.getProofFor(f);
}

TrustNode AlphaEqVariantProofGenerator::convertEq(TrustNode eqt)
{
  Node eq = eqt.getProven();
  Assert(eq.getKind() == EQUAL);
  AlphaEqVariantNodeConverter aevnc;
  Node rhs = eq[1];
  if (!expr::hasBoundVar(rhs))
  {
    // no need to convert
    return eqt;
  }
  Node rhsc = aevnc.convert(rhs);
  Node aeq = rhs.eqNode(rhsc);
  Node finalEq = eq[0].eqNode(rhsc);
  d_proof.addLazyStep(eq, eqt.getGenerator());
  std::vector<Node> aeqArgs;
  aeqArgs.push_back(rhs);
  const std::map<Node, Node>& vmap = aevnc.getVariableMapping();
  for (const std::pair<const Node, Node>& v : vmap)
  {
    aeqArgs.push_back(v.first.eqNode(v.second));
  }
  d_proof.addStep(aeq, PfRule::ALPHA_EQUIV, {}, aeqArgs);
  d_proof.addStep(finalEq, PfRule::TRANS, {eq, aeq}, {});
  return eqt;
}

std::string AlphaEqVariantProofGenerator::identify() const { return d_name; }

}  // namespace cvc5
