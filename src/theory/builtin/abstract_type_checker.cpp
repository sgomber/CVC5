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
 * Implements the type checker for APPLY_ABSTRACT
 */

#include "theory/builtin/abstract_type_checker.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

TypeNode AbstractTypeChecker::compute(TNode n, bool check)
{
  Assert(n.getKind() == APPLY_ABSTRACT);
  const ApplyAbstractOp& aao = n.getOperator().getConst<ApplyAbstractOp>();
  std::vector<Node> children(n.begin(), n.end());
  return computeAbstractApp(aao.getKind(), children, check);
}

TypeNode AbstractTypeChecker::computeAbstractApp(
    Kind k, const std::vector<Node>& children, bool check)
{
  std::vector<TypeNode> childrenTypes;
  std::vector<Kind> ctks;
  bool hasAbstract = false;
  for (const Node& nc : children)
  {
    TypeNode nct = nc.getType(check);
    childrenTypes.push_back(nct);
    Assert(!nct.isNull());
    if (nct.isAbstract())
    {
      hasAbstract = true;
      ctks.push_back(nct.getAbstractKind());
    }
    else
    {
      ctks.push_back(nct.getKind());
    }
  }
  if (!hasAbstract)
  {
    // there are no abstract children, should not use APPLY_ABSTRACT
    return TypeNode::null();
  }
  Kind ak = UNDEFINED_KIND;

  // TODO: abstract type rules

  if (ak == UNDEFINED_KIND)
  {
    return TypeNode::null();
  }
  return NodeManager::currentNM()->mkAbstractType(ak);
}

}  // namespace cvc5::internal
