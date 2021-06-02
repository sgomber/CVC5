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

#include "options/quantifiers_options.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/term_registry.h"

using namespace cvc5::kind;
using namespace cvc5::context;

namespace cvc5 {
namespace theory {
namespace quantifiers {

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

void OracleEngine::registerQuantifier(Node q)
{
}

void OracleEngine::check(Theory::Effort e, QEffort quant_e)
{
}

std::string OracleEngine::identify() const
{
  return std::string("OracleEngine");
}

void OracleEngine::declareOracleFun(Node f)
{
  
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
