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

#include "theory/quantifiers/quantifiers_state.h"
#include "theory/uf/equality_engine.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

InstDriver::InstDriver(Env& env,
                       State& state,
                       QuantifiersState& qs,
                       TermRegistry& tr)
    : EnvObj(env), d_state(state), d_qstate(qs), d_treg(tr)
{
}

void InstDriver::check(const std::vector<TNode>& quants)
{
  // TODO: compute levels of variables
  d_levels.clear();
  std::vector<TNode> fvars = d_state.getActiveFreeVarList();
}

bool InstDriver::isFinished() const { return d_state.isFinished(); }

void InstDriver::assignVar(TNode v, TNode eqc)
{
  Node eq = v.eqNode(eqc);
  d_qstate.getEqualityEngine()->assertEquality(eq, true, eq);
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
