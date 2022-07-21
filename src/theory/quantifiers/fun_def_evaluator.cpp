/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of techniques for evaluating terms with recursively
 * defined functions.
 */

#include "theory/quantifiers/fun_def_evaluator.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

FunDefEvaluator::FunDefEvaluator(Env& env) : EnvObj(env) {}

void FunDefEvaluator::assertDefinition(Node q)
{
  Trace("fd-eval") << "FunDefEvaluator: assertDefinition " << q << std::endl;
  Node h = QuantAttributes::getFunDefHead(q);
  if (h.isNull())
  {
    // not a function definition
    return;
  }
  // h possibly with zero arguments?
  Node f = h.hasOperator() ? h.getOperator() : h;
  Assert(d_funDefMap.find(f) == d_funDefMap.end())
      << "FunDefEvaluator::assertDefinition: function already defined";
  d_funDefs.push_back(q);
  FunDefInfo& fdi = d_funDefMap[f];
  fdi.d_quant = q;
  fdi.d_body = QuantAttributes::getFunDefBody(q);
  Assert(!fdi.d_body.isNull());
  fdi.d_args.insert(fdi.d_args.end(), q[0].begin(), q[0].end());
  Trace("fd-eval") << "FunDefEvaluator: function " << f << " is defined with "
                   << fdi.d_args << " / " << fdi.d_body << std::endl;
}

Node FunDefEvaluator::evaluateDefinitions(Node n)
{
  Trace("fd-eval") << "FunDefEvaluator: evaluateDefinitions " << n << std::endl;
  Node curr = n;
  for (size_t i = 0; i < options().quantifiers.sygusRecFunEvalLimit; i++)
  {
    Node prev = curr;
    // expand definitions, with rewriting
    clearCaches();
    curr = convert(curr);
    Trace("fd-eval-debug") << "...rewritten (" << i << "):" << curr
                           << std::endl;
    // if constant, we are done
    if (curr.isConst() || prev ==curr)
    {
      Trace("fd-eval") << "...return " << curr << std::endl;
      return curr;
    }
  }
  Trace("fd-eval") << "...failed, return original" << std::endl;
  return n;
}

Node FunDefEvaluator::preConvert(Node n)
{
  // must rename variables to ensure variable shadowing issues don't arise
  // when evaluating recursive functions with nested quantifiers
  if (n.isClosure())
  {
    std::vector<Node> vars(n[0].begin(), n[0].end());
    std::vector<Node> subs;
    NodeManager * nm = NodeManager::currentNM();
    for (const Node& v : vars)
    {
      subs.push_back(nm->mkBoundVar(v.getType()));
    }
    return n.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
  }
  return n;
}

Node FunDefEvaluator::postConvert(Node n)
{
  n = rewrite(n);
  Trace("fd-eval-debug2") << "Post-convert " << n << std::endl;
  if (n.getKind() != APPLY_UF)
  {
    // not an application of a recursive function
    return n;
  }
  // need to evaluate it
  Node f = n.getOperator();
  std::map<Node, FunDefInfo>::const_iterator itf = d_funDefMap.find(f);
  if (itf == d_funDefMap.end())
  {
    return n;
  }
  // get the function definition
  Node sbody = itf->second.d_body;
  const std::vector<Node>& args = itf->second.d_args;
  std::vector<Node> children(n.begin(), n.end());
  // invoke it on arguments using the evaluator, which will rewrite
  sbody = evaluate(sbody, args, children);
  Trace("fd-eval-debug2") << "...expand to " << sbody << std::endl;
  Assert(!sbody.isNull());
  return sbody;
}

bool FunDefEvaluator::hasDefinitions() const { return !d_funDefMap.empty(); }

const std::vector<Node>& FunDefEvaluator::getDefinitions() const
{
  return d_funDefs;
}
Node FunDefEvaluator::getDefinitionFor(Node f) const
{
  std::map<Node, FunDefInfo>::const_iterator it = d_funDefMap.find(f);
  if (it != d_funDefMap.end())
  {
    return it->second.d_quant;
  }
  return Node::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
