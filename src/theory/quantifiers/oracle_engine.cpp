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
 * Oracle engine
 */

#include "theory/quantifiers/oracle_engine.h"

#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/quantifiers_attributes.h"

using namespace cvc5::kind;
using namespace cvc5::context;

namespace cvc5 {
namespace theory {
namespace quantifiers {

/** Attribute true for input variables */
struct OracleInputVarAttributeId
{
};
typedef expr::Attribute<OracleInputVarAttributeId, bool>
    OracleInputVarAttribute;
/** Attribute true for output variables */
struct OracleOutputVarAttributeId
{
};
typedef expr::Attribute<OracleOutputVarAttributeId, bool>
    OracleOutputVarAttribute;

OracleEngine::OracleEngine(QuantifiersState& qs,
                           QuantifiersInferenceManager& qim,
                           QuantifiersRegistry& qr,
                           TermRegistry& tr)
    : QuantifiersModule(qs, qim, qr, tr)
{
}

void OracleEngine::presolve() {}

bool OracleEngine::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void OracleEngine::reset_round(Theory::Effort e) {}

void OracleEngine::registerQuantifier(Node q) {}

void OracleEngine::check(Theory::Effort e, QEffort quant_e) {}

void OracleEngine::checkOwnership(Node q)
{
  // take ownership of quantified formulas that are oracle interfaces
  QuantAttributes& qa = d_qreg.getQuantAttributes();
  if (qa.isOracleInterface(q))
  {
    d_qreg.setOwner(q, this, 2);
  }
}

std::string OracleEngine::identify() const
{
  return std::string("OracleEngine");
}

void OracleEngine::declareOracleFun(Node f) { d_oracleFuns.push_back(f); }

Node mkOracleInterface(const std::vector<Node>& inputs,
                       const std::vector<Node>& outputs,
                       Node assume,
                       Node constraint,
                       const std::string& binName)
{
  Assert(!assume.isNull());
  Assert(!constraint.isNull());
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  OracleInterfaceAttribute oia;
  Node oiVar = sm->mkDummySkolem("oracle-interface", nm->booleanType());
  oiVar.setAttribute(oia, binName);
  Node ipl = nm->mkNode(INST_PATTERN_LIST, nm->mkNode(INST_ATTRIBUTE, oiVar));
  std::vector<Node> vars;
  OracleInputVarAttribute oiva;
  for (Node v : inputs)
  {
    v.setAttribute(oiva, true);
    vars.push_back(v);
  }
  OracleInputVarAttribute oova;
  for (Node v : outputs)
  {
    v.setAttribute(oova, true);
    vars.push_back(v);
  }
  Node bvl = nm->mkNode(BOUND_VAR_LIST, vars);
  Node body = nm->mkNode(ORACLE_INTERFACE, assume, constraint);
  return nm->mkNode(FORALL, bvl, body, ipl);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
