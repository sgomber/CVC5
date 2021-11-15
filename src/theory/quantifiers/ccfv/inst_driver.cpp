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

#include "theory/quantifiers/ccfv/inst_driver.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

InstDriver::InstDriver(Env& env,
                       State& state,
                       QuantifiersState& qs,
                       TermRegistry& tr)
    : EnvObj(env), d_state(state), d_qstate(qs), d_treg(tr)
{
}

void InstDriver::check(Theory::Effort e, QEffort quant_e)
{
  // TODO: compute levels of variables
  
  
  FirstOrderModel* fm = d_treg.getModel();
  for (size_t i = 0, nquant = fm->getNumAssertedQuantifiers(); i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i);
    if (!d_qreg.hasOwnership(q, this))
    {
      continue;
    }
    activateQuantifier(q);
  }
  
  /*
  do
  {
    TNode v = getNextVariable();
    if (!v.isNull())
    {
      decideVar(v);
    }
    // otherwise increment current
  } while (!d_stack.empty());
  */
}

bool InstDriver::isFinished() const { return false; }

TNode InstDriver::getNextVariable() { return TNode::null(); }

void InstDriver::pushVar(TNode v)
{
  /*
  // push a context
  // context().push();
  d_varStack.push_back(v);

  const FreeVarInfo& fvi = getFreeVarInfo(v);
  fvi.resetDomain();

  // compute the equivalence classes we should assign
  // compute d_eqcDomain
  // TODO: based on top-down matching?

  // decrement the # assigned variables in each term that contains it, which
  // also computes which terms are newly fully assigned. These are stored in
  // d_fullyAssignedPat.
  for (TNode pat : fvi.d_useList)
  {
    const PatTermInto& pti = getPatternTermInfo(p);
    Assert(pti.d_numUnassignVar > 0);
    pti.d_numUnassignVar = pti.d_numUnassignVar - 1;
    if (pti.d_numUnassignVar == 0)
    {
      fvi.d_fullyAssignedPat.push_back(pat);
    }
  }
  */
}

void InstDriver::popVar()
{
  /*
  Assert(!d_varStack.empty());

  TNode v = d_varStack.back();

  d_varStack.pop_back();
  */
}

void InstDriver::assignVar(TNode v,
                           TNode eqc,
                           std::vector<TNode>& fullyAssignedPats)
{
  Node eq = v.eqNode(eqc);
  d_ee->assertEquality(eq);
  // may be finished
  if (d_state.isFinished())
  {
    return;
  }
  /*
  const FreeVarInfo& fvi = getFreeVarInfo(v);
  // for each fully assigned pattern, if they are not fully assigned, we mark
  // them as dead
  for (TNode p : fvi.d_fullAssignedPats)
  {
    notifyPatternEqGround(p, d_null);
    // if all quantified formulas are inactive, finish
    if (isFinished())
    {
      break;
    }
  }
  */
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
