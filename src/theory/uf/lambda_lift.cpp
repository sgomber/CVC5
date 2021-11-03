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
 * Implementation of lambda lifting.
 */

#include "theory/uf/lambda_lift.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/uf_options.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace uf {

LambdaLift::LambdaLift(Env& env) : EnvObj(env), d_processed(userContext()) {}

TrustNode LambdaLift::lift(Node node)
{
  if (d_processed.find(node) != d_processed.end())
  {
    return TrustNode::null();
  }
  d_processed.insert(node);
  Node assertion = getAssertionFor(node);
  if (assertion.isNull())
  {
    return TrustNode::null();
  }
  // TODO: proofs
  return TrustNode::mkTrustLemma(assertion);
}

TrustNode LambdaLift::ppRewrite(Node node, std::vector<SkolemLemma>& lems)
{
  TNode skolem = getSkolemFor(node);
  if (skolem.isNull())
  {
    return TrustNode::null();
  }
  if (!options().uf.ufHoLazyLambdaLift)
  {
    TrustNode trn = lift(node);
    lems.push_back(SkolemLemma(trn, skolem));
  }
  // TODO: proofs
  return TrustNode::mkTrustRewrite(node, skolem);
}

Node LambdaLift::getAssertionFor(TNode node)
{
  TNode skolem = getSkolemFor(node);
  if (skolem.isNull())
  {
    return Node::null();
  }
  Kind k = node.getKind();
  Node assertion;
  if (k == LAMBDA)
  {
    NodeManager* nm = NodeManager::currentNM();
    // The new assertion
    std::vector<Node> children;
    // bound variable list
    children.push_back(node[0]);
    // body
    std::vector<Node> skolem_app_c;
    skolem_app_c.push_back(skolem);
    skolem_app_c.insert(skolem_app_c.end(), node[0].begin(), node[0].end());
    Node skolem_app = nm->mkNode(APPLY_UF, skolem_app_c);
    children.push_back(skolem_app.eqNode(node[1]));
    // axiom defining skolem
    assertion = nm->mkNode(FORALL, children);

    // Lambda lifting is trivial to justify, hence we don't set a proof
    // generator here. In particular, replacing the skolem introduced
    // here with its original lambda ensures the new assertion rewrites
    // to true.
    // For example, if (lambda y. t[y]) has skolem k, then this lemma is:
    //   forall x. k(x)=t[x]
    // whose witness form rewrites
    //   forall x. (lambda y. t[y])(x)=t[x] --> forall x. t[x]=t[x] --> true
  }
  else if (k == WITNESS)
  {
    Assert(node[0].getNumChildren() == 1);

    // The new assertion is the assumption that the body
    // of the witness operator holds for the Skolem
    assertion = node[1].substitute(node[0][0], skolem);
  }
  return assertion;
}

Node LambdaLift::getSkolemFor(TNode node)
{
  Node skolem;
  Kind k = node.getKind();
  if (k == LAMBDA)
  {
    // if a lambda, do lambda-lifting
    if (!expr::hasFreeVar(node))
    {
      Trace("rtf-proof-debug")
          << "RemoveTermFormulas::run: make LAMBDA skolem" << std::endl;
      // Make the skolem to represent the lambda
      NodeManager* nm = NodeManager::currentNM();
      SkolemManager* sm = nm->getSkolemManager();
      skolem = sm->mkPurifySkolem(
          node,
          "lambdaF",
          "a function introduced due to term-level lambda removal",
          SkolemManager::SKOLEM_LAMBDA_VAR);
    }
  }
  else if (k == WITNESS)
  {
    // If a witness choice
    //   For details on this operator, see
    //   http://planetmath.org/hilbertsvarepsilonoperator.
    if (!expr::hasFreeVar(node))
    {
      // Make the skolem to witness the choice, which notice is handled
      // as a special case within SkolemManager::mkPurifySkolem.
      NodeManager* nm = NodeManager::currentNM();
      SkolemManager* sm = nm->getSkolemManager();
      skolem = sm->mkPurifySkolem(
          node,
          "witnessK",
          "a skolem introduced due to term-level witness removal");
    }
  }
  return skolem;
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5
