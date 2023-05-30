/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sygus_module.
 */

#include "theory/quantifiers/sygus/sygus_module.h"

#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusModule::SygusModule(Env& env,
                         QuantifiersState& qs,
                         QuantifiersInferenceManager& qim,
                         TermDbSygus* tds,
                         SynthConjecture* p)
    : EnvObj(env), d_qstate(qs), d_qim(qim), d_tds(tds), d_parent(p)
{
}

bool SygusModule::isTypeOk(const std::vector<Node>& candidate_values) const
{
  // check the side condition if we constructed a candidate
  Node quant = d_parent->getConjecture();
  Trace("sygus-engine-debug") << "Check types" << std::endl;
  // check type constraints
  for (size_t i = 0, size = candidate_values.size(); i < size; i++)
  {
    const TypeNode& stn =
        candidate_values[i].getType().getDType().getSygusType();
    if (!stn.isAbstract())
    {
      continue;
    }
    // check if the type is met
    Node bnv = d_tds->sygusToBuiltin(candidate_values[i]);
    TypeNode expectedRange = quant[0][i].getType();
    if (expectedRange.isFunction())
    {
      expectedRange = expectedRange.getRangeType();
    }
    if (bnv.getType() != expectedRange)
    {
      Trace("sygus-engine")
          << "...failed type " << bnv << " : " << bnv.getType() << ", expected "
          << expectedRange << std::endl;
      d_parent->excludeCurrentSolution(
          candidate_values,
          InferenceId::QUANTIFIERS_SYGUS_RETURN_TYPE_EXCLUDE_CURRENT);
      return false;
    }
  }
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
