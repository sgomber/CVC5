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

#include "expr/node_algorithm.h"

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

Node AlphaEqVariantProofGenerator::convert(Node n)
{
  if (!expr::hasBoundVar(n))
  {
    // no need to convert
    return n;
  }
  AlphaEqVariantNodeConverter aevnc;
  Node nc = aevnc.convert(n);
  std::vector<Node> aeqArgs;
  aeqArgs.push_back(n);
  const std::map<Node, Node>& vmap = aevnc.getVariableMapping();
  for (const std::pair<const Node, Node>& v : vmap)
  {
    aeqArgs.push_back(v.first.eqNode(v.second));
  }
  Node aeq = n.eqNode(nc);
  d_proof.addStep(aeq, PfRule::ALPHA_EQUIV, {}, aeqArgs);
  return nc;
}

ProofGenerator * AlphaEqVariantProofGenerator::convertEq(Node lhs, Node& rhs, ProofGenerator * pg)
{
  Node rhsc = convert(rhs);
  if (rhs==rhsc || pg == nullptr)
  {
    // no proofs or no change, just return
    rhs = rhsc;
    return pg;
  }
  Node eq = lhs.eqNode(rhs);
  Node finalEq = lhs.eqNode(rhsc);
  d_proof.addLazyStep(eq, pg);
  Node aeq = rhs.eqNode(rhsc);
  d_proof.addStep(finalEq, PfRule::TRANS, {eq, aeq}, {});
  
  rhs = rhsc;
  return this;
}

std::string AlphaEqVariantProofGenerator::identify() const { return d_name; }

}  // namespace cvc5
