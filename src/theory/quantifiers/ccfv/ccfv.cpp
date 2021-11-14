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

using namespace cvc5::kind;

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

void CongruenceClosureFv::registerQuantifier(Node q) {}

void CongruenceClosureFv::assertNode(Node q)
{
  Assert(q.getKind() == FORALL);
  QuantInfo& qi = d_state.getOrMkQuantInfo(q, d_qstate.getEqualityEngine(), d_tcanon);
  // its pattern terms are registered
  const std::map<TNode, std::vector<Node>>& ms = qi.getConstraints();
  for (TNode p : ms)
  {
    registerMatchTerm(p, q);
  }
}

void CongruenceClosureFv::registerMatchTerm(TNode p, TNode q)
{
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();

  // we will notify the quantified formula when the pattern becomes set
  PatternTerm& pi = d_state.getOrMkPatTermInfo(p);
  pi.d_parentNotify.push_back(q);

  // Now, traverse p. This sets up the pattern info for subterms of p.
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
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
      visited.insert(cur);
      if (!expr::hasFreeVar(cur))
      {
        continue;
      }
      Kind k = cur.getKind();
      if (k == BOUND_VARIABLE)
      {
        freeVars.push_back(cur);
        continue;
      }
      Assert(cur.getNumChildren() > 0);
      // compute if Boolean connective
      bool isBoolConnective = expr::isBooleanConnective(cur);
      if (!isBoolConnective && !ee->isFunctionKind(k))
      {
        // not handled as Boolean connective or congruence kind
        continue;
      }
      for (TNode cc : cur)
      {
        if (!expr::hasFreeVar(cc))
        {
          continue;
        }
        PatternTerm& pi = d_state.getOrMkPatTermInfo(cc);
        if (isBoolConnective)
        {
          // Boolean connectives require notifications to parent
          pi.d_parentNotify.push_back(cur);
        }
        else
        {
          // Other terms will track # total unassigned free variables
          parentList[cc].push_back(cur);
          // Boolean connectives require notifications to parent
          pi.d_parentCongNotify.push_back(cur);
        }
        visit.push_back(cc);
      }
    }
  } while (!visit.empty());

  // go back and set the use list of the free variables
  std::map<TNode, std::vector<TNode> >::iterator itpl;
  std::unordered_set<TNode>::iterator it;
  for (TNode v : freeVars)
  {
    FreeVarInfo& fi = d_state.getOrMkFreeVarInfo(v);
    std::unordered_set<TNode> containing;
    TNode cur;
    visit.push_back(v);
    do
    {
      cur = visit.back();
      visit.pop_back();
      it = containing.find(cur);
      if (it == containing.end())
      {
        containing.insert(cur);
        if (fi.d_useList.find(cur) == fi.d_useList.end())
        {
          fi.d_useList.push_back(cur);
          PatternTerm& pi = d_state.getOrMkPatTermInfo(cur);
          pi.d_numUnassigned = pi.d_numUnassigned + 1;
        }
        itpl = parentList.find(cur);
        if (itpl != parentList.end())
        {
          visit.insert(visit.end(), itpl->second.begin(), itpl->second.end());
        }
      }
    } while (!containing.empty());
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
