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

using namespace cvc5::internal::kind;

namespace cvc5::internal {
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
      d_driver(env, d_state, qs, qim, tr),
      d_registeredTerms(context())
{
}

bool CongruenceClosureFv::needsCheck(Theory::Effort e)
{
  return (e == Theory::EFFORT_FULL);
}

void CongruenceClosureFv::reset_round(Theory::Effort e) {}

void CongruenceClosureFv::check(Theory::Effort e, QEffort quant_e)
{
  CodeTimer codeTimer(d_qstate.getStats().d_ccfvTime);
  if (quant_e != QEFFORT_CONFLICT)
  {
    return;
  }
  double clSet = 0;
  if (TraceIsOn("ccfv-engine"))
  {
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("ccfv-engine")
        << "---Congruence Closure with Free Variables Round, effort = " << e
        << "---" << std::endl;
  }
  std::vector<TNode> quants;
  FirstOrderModel* fm = d_treg.getModel();
  for (size_t i = 0, nquant = fm->getNumAssertedQuantifiers(); i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i, true);
    if (!d_qreg.hasOwnership(q, this))
    {
      continue;
    }
    quants.push_back(q);
  }
  // run with the instantiation driver
  if (!quants.empty())
  {
    d_driver.check(quants);
  }

  if (TraceIsOn("ccfv-engine"))
  {
    double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("ccfv-engine") << "Finished ccfv, time = " << (clSet2 - clSet);
    Trace("ccfv-engine") << ", #inst = " << d_driver.numFoundInst();
    if (d_driver.inConflict())
    {
      Trace("ccfv-engine") << ", conflict";
    }
    Trace("ccfv-engine") << std::endl;
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
  // (1) variables to quantifiers
  // (2) notifications from constraint terms to quantified formulas
  // (3) notifications from children to congruence terms
  // (4) notifications from children to other terms (including Boolean
  // connectives and theory symbols that we do not do congruence over)
  // (5) free variables to "final" terms that are fully assigned when we
  // assign that variable. This includes ground terms, that are notified
  // by the null variable at the beginning of the search.
  // (6) marking "watched evaluate" terms, e.g. (+ x 1) in (P (+ x 1)).

  // get the equality engine
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  // initialize the internal information for the quantified formula
  QuantInfo& qi = d_state.initializeQuantInfo(q, d_tcanon);
  // free variables from the quantified formula
  const std::vector<TNode>& fvars = qi.getOrderedFreeVariables();
  for (TNode v : fvars)
  {
    // (1) remember that this variable is contained in q
    FreeVarInfo& fi = d_state.getOrMkFreeVarInfo(v);
    fi.d_quantList.push_back(q);
  }

  NodeSet::const_iterator it;
  std::vector<TNode> visit;

  // we traverse its constraint terms to set up the parent notification lists
  const std::vector<TNode>& cterms = qi.getConstraintTerms();
  for (TNode c : cterms)
  {
    // we will notify the quantified formula when the pattern becomes set
    PatTermInfo& pi = d_state.getOrMkPatTermInfo(c);
    // (2) when the constraint term is assigned, we notify q
    pi.d_parentNotify.push_back(q);
    // we visit the constraint term below
    visit.push_back(c);
  }

  TNode cur;
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_registeredTerms.find(cur);
    if (it == d_registeredTerms.end())
    {
      d_registeredTerms.insert(cur);
      if (!expr::hasBoundVar(cur) || !QuantInfo::isTraverseTerm(cur))
      {
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
      bool isCongKind = ee->isFunctionKind(k);
      for (TNode cc : cur)
      {
        PatTermInfo& pi = d_state.getOrMkPatTermInfo(cc);
        if (isCongKind)
        {
          Assert(ee->isFunctionKind(k));
          Assert(cur.hasOperator());
          // (3) congruence terms will recieve notifications when unassigned
          pi.d_parentCongNotify.push_back(cur);
        }
        else
        {
          // (4) other kinds require notifications to parent
          pi.d_parentNotify.push_back(cur);
        }
        visit.push_back(cc);
      }
    }
  } while (!visit.empty());

  // (5) map free variables to terms that are fully assigned when that free
  // variable is assigned
  const std::map<TNode, std::vector<TNode>>& vft = qi.getVarToFinalTermMap();
  for (const std::pair<const TNode, std::vector<TNode>>& tv : vft)
  {
    FreeVarInfo& fi = d_state.getOrMkFreeVarInfo(tv.first);
    for (TNode ft : tv.second)
    {
      fi.d_finalTerms.insert(ft);
    }
  }
  // (6) mark evaluate arg terms as watching evaluation. This is for terms
  // (P (+ x 1)), when x becomes assigned to e.g. 100, we rewrite (+ x 1)
  // to 101; if 101 is a term in the equivalence class, we merge (+ x 1) and
  // 101.
  const std::vector<TNode>& eat = qi.getEvalArgTerms();
  for (TNode et : eat)
  {
    PatTermInfo& pi = d_state.getOrMkPatTermInfo(et);
    pi.d_isWatchedEval = true;
  }
}

void CongruenceClosureFv::preRegisterQuantifier(Node q) {}

std::string CongruenceClosureFv::identify() const
{
  return "CongruenceClosureFv";
}

State* CongruenceClosureFv::getState() { return &d_state; }

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
