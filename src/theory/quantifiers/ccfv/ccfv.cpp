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

void CongruenceClosureFv::registerQuantifier(Node q) {}

void CongruenceClosureFv::preRegisterQuantifier(Node q) {}

std::string CongruenceClosureFv::identify() const { return "CongruenceClosureFv"; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
