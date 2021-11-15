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

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
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
                                         TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_state(env, qs, getTermDatabase()),
      d_driver(env, d_state, qs, tr)
{
}

bool CongruenceClosureFv::needsCheck(Theory::Effort e)
{
  bool performCheck = false;
  if (options().quantifiers.quantConflictFind)
  {
    if (e == Theory::EFFORT_LAST_CALL)
    {
      performCheck =
          options().quantifiers.qcfWhenMode == options::QcfWhenMode::LAST_CALL;
    }
    else if (e == Theory::EFFORT_FULL)
    {
      performCheck =
          options().quantifiers.qcfWhenMode == options::QcfWhenMode::DEFAULT;
    }
    else if (e == Theory::EFFORT_STANDARD)
    {
      performCheck =
          options().quantifiers.qcfWhenMode == options::QcfWhenMode::STD;
    }
  }
  return performCheck;
}

void CongruenceClosureFv::reset_round(Theory::Effort e) {}

void CongruenceClosureFv::check(Theory::Effort e, QEffort quant_e)
{
  std::vector<TNode> quants;
  FirstOrderModel* fm = d_treg.getModel();
  for (size_t i = 0, nquant = fm->getNumAssertedQuantifiers(); i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i, true);
    if (!d_qreg.hasOwnership(q, this))
    {
      return;
    }
    quants.push_back(q);
  }
  // run with the instantiation driver
  if (!quants.empty())
  {
    d_state.resetRound(quants.size());
    d_driver.check(quants);
  }
}

void CongruenceClosureFv::registerQuantifier(Node q) {}

void CongruenceClosureFv::assertNode(Node q)
{
  Assert(q.getKind() == FORALL);
  if (!d_qreg.hasOwnership(q, this))
  {
    return;
  }
  // Assert quantified formula. This sets up:
  // (1) notifications from constraint terms to quantified formulas
  // (2) notifications from children to Boolean connectives
  // (3) notifications from children to congruence terms
  // (4) free variables to use list terms
  // (5) addition of congruence terms to the equality engine

  // get the equality engine
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  // initialize the internal information for the quantified formula
  QuantInfo& qi = d_state.initializeQuantInfo(q, ee, d_tcanon);
  // free variables from the quantified formula
  const std::vector<TNode>& fvars = qi.getOrderedFreeVariables();
  for (TNode v : fvars)
  {
    // (*)
    FreeVarInfo& fi = d_state.getOrMkFreeVarInfo(v);
    fi.d_quantList.push_back(q);
  }

  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
  std::vector<TNode> visit;

  // we traverse its constraint terms to set up the parent notification lists
  const std::vector<TNode>& cterms = qi.getConstraintTerms();
  for (TNode c : cterms)
  {
    // we will notify the quantified formula when the pattern becomes set
    PatTermInfo& pi = d_state.getOrMkPatTermInfo(c);
    // (1) when the constraint term is assigned, we notify q
    pi.d_parentNotify.push_back(q);
    // we visit the constraint term below
    visit.push_back(c);
  }

  TNode cur;
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
        // FIXME: require initial notifications for these terms
        // does not contain free variables, we don't require
        continue;
      }
      Kind k = cur.getKind();
      if (k == BOUND_VARIABLE)
      {
        // should be one of the free variables of the quantified formula
        Assert(std::find(fvars.begin(), fvars.end(), cur) != fvars.end());
        continue;
      }
      Assert(cur.getNumChildren() > 0);
      bool isBoolConnective = false;
      // Node matchOp;
      if (ee->isFunctionKind(k))
      {
        // matchOp = getTermDatabase()->getMatchOperator(cur);
      }
      else
      {
        // compute if Boolean connective
        if (!expr::isBooleanConnective(cur))
        {
          // not handled as Boolean connective or congruence kind, skip
          continue;
        }
        isBoolConnective = true;
      }
      for (TNode cc : cur)
      {
        PatTermInfo& pi = d_state.getOrMkPatTermInfo(cc);
        if (isBoolConnective)
        {
          // (2) Boolean connectives require notifications to parent
          pi.d_parentNotify.push_back(cur);
        }
        else
        {
          Assert(ee->isFunctionKind(k));
          Assert(cur.hasOperator());
          // (3) congruence terms will recieve notifications when unassigned
          pi.d_parentCongNotify.push_back(cur);
          /*
          if (cc.getKind()==BOUND_VARIABLE && !matchOp.isNull())
          {
            // if a bound variable, we track that the quantified formula may
            // want to match this position
            FreeVarInfo& fi = d_state.getOrMkFreeVarInfo(cc);
            fi.addQuantMatch(matchOp, i, q);
          }
          */
        }
        visit.push_back(cc);
      }
    }
  } while (!visit.empty());

  // (4) map free variables to terms that are fully assigned when that free
  // variable is assigned
  const std::map<TNode, TNode>& termToMaxVar = qi.getTermMaxVarMap();
  for (const std::pair<const TNode, TNode>& tv : termToMaxVar)
  {
    FreeVarInfo& fi = d_state.getOrMkFreeVarInfo(tv.second);
    fi.d_useList.insert(tv.first);
  }

  // (5) add the congruence terms to the equality engine
  const std::vector<TNode>& pterms = qi.getCongruenceTerms();
  for (TNode p : pterms)
  {
    ee->addTerm(p);
    // should now exist in the equality engine, and not have a value
    Assert(ee->hasTerm(p));
    Assert(d_state.getValue(p).isNull());
  }
}

void CongruenceClosureFv::preRegisterQuantifier(Node q) {}

std::string CongruenceClosureFv::identify() const
{
  return "CongruenceClosureFv";
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
