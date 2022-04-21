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
 * Inst evaluator class.
 */

#include "theory/quantifiers/inst_evaluator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstEvaluator::InstEvaluator(Node q) : d_quant(q)
{
  Assert (q.getKind()==kind::FORALL);
}

bool InstEvaluator::initialize()
{
  Assert (d_evalBody.empty());
  d_currInfeasible = false;
  d_currVar = TNode::null();
  d_currSubs = TNode::null();
  // convert and push the body
  return convertAndPush(d_quant[1]);
}

bool InstEvaluator::push(TNode v, TNode s)
{
  Assert (!d_evalBody.empty());
  Assert (d_evalBody.size()<=d_quant[0].getNumChildren());
  Assert (d_quant[0][d_evalBody.size()-1] == v);
  Node curr = d_evalBody.back();
  d_currVar = v;
  d_currSubs = s;
  return convertAndPush(curr);
}

bool InstEvaluator::convertAndPush(Node body)
{
  Node cbody = convert(body);
  if (d_currInfeasible)
  {
    return false;
  }
  d_evalBody.push_back(cbody);
  return true;
}

void InstEvaluator::pop()
{
  Assert (!d_evalBody.empty());
  d_evalBody.pop_back();
}

bool InstEvaluator::shouldTraverse(Node n)
{
  if (d_currInfeasible)
  {
    // don't traverse further if already infeasible
    return false;
  }
  // never traverse ground terms, unless we are initializing?
  return true;
}

Node InstEvaluator::postConvert(Node n)
{
  if (d_currInfeasible)
  {
    return n;
  }
  Node neval = evaluateInternal(n, d_currVar, d_currSubs, d_currInfeasible);
  return neval;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

