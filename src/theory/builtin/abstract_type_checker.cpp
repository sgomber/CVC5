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

namespace cvc5::internal {

TypeNode AbstractTypeChecker::compute(TNode n, bool check)
{
  Assert(n.getKind() == kind::APPLY_ABSTRACT);
  const ApplyAbstractOp& aao = n.getOperator().getConst<ApplyAbstractOp>();
  std::vector<TypeNode> childrenTypes;
  for (const Node& nc : n)
  {
    childrenTypes.push_back(nc.getType(check));
  }
  return computeInternal(aao, childrenTypes);
}

TypeNode AbstractTypeChecker::computeInternal(
    const ApplyAbstractOp& aao, const std::vector<TypeNode>& childTypes)
{
  Kind ak = ABSTRACT_TYPE;
  
  // TODO: more precise type rules?

  return NodeManager::currentNM()->mkAbstractType(ak);
}

}  // namespace cvc5::internal
