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
  // we will notify the quantified formula when the pattern becomes set
  PatternTerm& pi = d_state.getOrMkPatTermInfo(p);
  pi.d_parentNotify.push_back(q);

  // Now, traverse p. This sets up the pattern info for subterms of p.
  std::unordered_map<TNode, bool> visited;
  std::unordered_map<TNode, bool>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  std::vector<TNode> freeVars;
  // parents list
  std::map<TNode, std::vector<TNode> > parentList;
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      if (!expr::hasFreeVar(cur))
      {
        visited[cur] = true;
        continue;
      }
      if (cur.getKind() == BOUND_VARIABLE)
      {
        visited[cur] = true;
        qi.addCongruenceTerm(cur);
        freeVars.push_back(cur);
        continue;
      }
      visited[cur] = false;
      Assert(cur.getNumChildren() > 0);
      bool isBoolConnective = expr::isBooleanConnective(cur);
      for (TNode cc : cur)
      {
        if (!expr::hasFreeVar(cc))
        {
          continue;
        }
        if (isBoolConnective)
        {
          // Boolean connectives require notifications to parent
          PatternTerm& pi = d_state.getOrMkPatTermInfo(cc);
          pi.d_parentNotify.push_back(cur);
        }
        else
        {
          // Other terms will track # total unassigned free variables
          parentList[cc].push_back(cur);
        }
        visit.push_back(cc);
      }
    }
    else if (!it->second)
    {
      visited[cur] = true;
      // we will add this term to the equality engine. We add at post-order
      // traversal to that the order of terms is correct, i.e. we add subterms
      // first.
      qi.addCongruenceTerm(cur);
    }
  } while (!visit.empty());

  // go back and set the use list of the free variables
  std::map<TNode, std::vector<TNode> >::iterator itpl;
  for (TNode v : freeVars)
  {
  }
}

void CongruenceClosureFv::preRegisterQuantifier(Node q) {}

std::string CongruenceClosureFv::identify() const
{
  return "CongruenceClosureFv";
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
