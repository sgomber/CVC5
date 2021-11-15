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

#include "options/quantifiers_options.h"
#include "expr/node_algorithm.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_registry.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

CongruenceClosureFv::CongruenceClosureFv(Env& env,
                                         QuantifiersState& qs,
                                         QuantifiersInferenceManager& qim,
                                         QuantifiersRegistry& qr,
                                         TermRegistry& tr) : QuantifiersModule(env, qs, qim, qr, tr), d_state(env, qs), d_driver(env, d_state, qs, tr)
{
}

bool CongruenceClosureFv::needsCheck(Theory::Effort e) { 
  bool performCheck = false;
  if( options().quantifiers.quantConflictFind ){
    if( e==Theory::EFFORT_LAST_CALL ){
      performCheck = options().quantifiers.qcfWhenMode == options::QcfWhenMode::LAST_CALL;
    }else if( e==Theory::EFFORT_FULL ){
      performCheck = options().quantifiers.qcfWhenMode == options::QcfWhenMode::DEFAULT;
    }else if( e==Theory::EFFORT_STANDARD ){
      performCheck = options().quantifiers.qcfWhenMode == options::QcfWhenMode::STD;
    }
  }
  return performCheck;
}

void CongruenceClosureFv::reset_round(Theory::Effort e) {}

void CongruenceClosureFv::check(Theory::Effort e, QEffort quant_e) 
{
  FirstOrderModel* fm = d_treg.getModel();
  for (size_t i = 0, nquant = fm->getNumAssertedQuantifiers(); i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i);
    if (!d_qreg.hasOwnership(q, this))
    {
      continue;
    }
    // activate the quantified formula
    d_state.initializeQuantInfo(q, d_qstate.getEqualityEngine(), d_tcanon);
    activateQuantifier(q);
  }
  // run with the instantiation driver
}

void CongruenceClosureFv::registerQuantifier(Node q) {}

void CongruenceClosureFv::assertNode(Node q)
{
  // eager?
  //Assert(q.getKind() == FORALL);
  //d_state.initializeQuantInfo(q, d_qstate.getEqualityEngine(), d_tcanon);
}

void CongruenceClosureFv::activateQuantifier(TNode q)
{
  Assert (q.getKind()==FORALL);
  QuantInfo& qi = d_state.getQuantInfo(q);

  // Now, traverse p. This sets up the pattern info for subterms of p.
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
  std::vector<TNode> visit;

  // its pattern terms are registered
  const std::vector<TNode>& cterms = qi.getConstraintTerms();
  const std::vector<TNode>& pterms = qi.getCongruenceTerms();
  const std::vector<TNode>& mterms = qi.getTopLevelMatchers();
  for (TNode c : cterms)
  {
    // we will notify the quantified formula when the pattern becomes set
    PatTermInfo& pi = d_state.getOrMkPatTermInfo(c);
    pi.d_parentNotify.push_back(q);
    // we visit the constraint term below
    visit.push_back(c);
  }

  // get the equality engine
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();

  TNode cur;
  std::vector<TNode> freeVars;
  // parents list
  std::map<TNode, std::vector<TNode>> parentList;
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
        PatTermInfo& pi = d_state.getOrMkPatTermInfo(cc);
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
  std::map<TNode, std::vector<TNode>>::iterator itpl;
  for (TNode v : freeVars)
  {
    FreeVarInfo& fi = d_state.getOrMkFreeVarInfo(v);
    std::unordered_set<TNode> containing;
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
          fi.d_useList.insert(cur);
          // increment the number of variables
          PatTermInfo& pi = d_state.getOrMkPatTermInfo(cur);
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
  
  // add the congruence terms to the equality engine
  for (TNode p : pterms)
  {
    ee->addTerm(p);
    // should now exist in the equality engine, and not have a value
    Assert (ee->hasTerm(p));
    Assert (d_state.getValue(p).isNull());
  }
}

void CongruenceClosureFv::preRegisterQuantifier(Node q) {}

std::string CongruenceClosureFv::identify() const
{
  return "CongruenceClosureFv";
}

}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
