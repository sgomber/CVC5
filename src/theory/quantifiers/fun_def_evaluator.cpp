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
  for (size_t i=0; i<options().quantifiers.sygusRecFunEvalLimit; i++)
  {
    // rewrite curr
    curr = rewrite(curr);
    Trace("fd-eval-debug") << "...rewritten (" << i << "):" << curr << std::endl;
    // if constant, we are done
    if (curr.isConst())
    {
      Trace("fd-eval") << "...return " << curr << std::endl;
      return curr;
    }
    // expand definitions
    curr = convert(curr);
    Trace("fd-eval-debug") << "...expanded (" << i << "):" << curr << std::endl;
  }
  Trace("fd-eval") << "...failed, return original" << std::endl;
  return n;
}

Node FunDefEvaluator::postConvert(Node n)
{
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
  if (!args.empty())
  {
    std::vector<Node> children(n.begin(), n.end());
    // invoke it on arguments using the evaluator, which will rewrite
    sbody = evaluate(sbody, args, children);
    Assert(!sbody.isNull());
  }
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
