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
 * Congruence closure with free variables
 */

#include "theory/quantifiers/ccfv/ccfv.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

CongruenceClosureFv::CongruenceClosureFv(Env& env,
                                         QuantifiersState& qs,
                                         QuantifiersInferenceManager& qim,
                                         QuantifiersRegistry& qr,
                                         TermRegistry& tr);

bool CongruenceClosureFv::needsCheck(Theory::Effort e) {}

QEffort CongruenceClosureFv::needsModel(Theory::Effort e) {}

void CongruenceClosureFv::reset_round(Theory::Effort e) {}

void CongruenceClosureFv::check(Theory::Effort e, QEffort quant_e) {}

void CongruenceClosureFv::registerQuantifier(Node q) 
{
  QuantInfo& qi = d_state.getOrMkQuantInfo(q, d_tcanon);
  // its pattern terms are registered
  const std::vector<TNode>& ms = qi.getMatchers();
  for (TNode p : ms)
  {
    registerMatchTerm(p, q, qi);
  }
}

void CongruenceClosureFv::registerMatchTerm(TNode p, TNode q, QuantInfo& qi)
{
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end()) {
      visited.insert(cur);
      if (expr::isBooleanConnective(cur))
      {
        // require notify from each child
        for (TNode cc : cur)
        {
          if (!expr::hasFreeVar(cc))
          {
            continue;
          }
          PatternTerm& pi = d_state.getOrMkPatTermInfo(cc);
          pi.d_parentNotify.push_back(cur);
          visit.push_back(cc);
        }
      }
      else if (expr::hasFreeVar(cur))
      {
        // we will add this term to the equality engine
        qi.addCongruenceTerm(cur);
        // traverse to its children
        if (cur.getNumChildren()>0)
        {
          visit.insert(visit.end(),cur.begin(),cur.end());
        }
      }
    }
  } while (!visit.empty());
  // we will notify the quantified formula
  PatternTerm& pi = d_state.getOrMkPatTermInfo(p);
  pi.d_parentNotify.push_back(q);
}

void CongruenceClosureFv::preRegisterQuantifier(Node q) {}

std::string CongruenceClosureFv::identify() const
{
  return "CongruenceClosureFv";
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
