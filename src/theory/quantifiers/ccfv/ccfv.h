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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__CCFV_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__CCFV_H

#include <unordered_map>
#include <unordered_set>

#include "expr/term_canonize.h"
#include "theory/quantifiers/ccfv/inst_driver.h"
#include "theory/quantifiers/ccfv/state.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ccfv {

/**
 * Congruence closure with free variables procedure
 *
 *

 TODO:
- account for unmatchable terms

 */
class CongruenceClosureFv : public QuantifiersModule
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  CongruenceClosureFv(Env& env,
                      QuantifiersState& qs,
                      QuantifiersInferenceManager& qim,
                      QuantifiersRegistry& qr,
                      TermRegistry& tr);

  bool needsCheck(Theory::Effort e) override;

  void reset_round(Theory::Effort e) override;

  void check(Theory::Effort e, QEffort quant_e) override;

  /* Called once for every quantifier 'q' globally (not dependent on context).
   */
  void registerQuantifier(Node q) override;

  /* Called once for every quantifier 'q' per context. */
  void preRegisterQuantifier(Node q) override;

  /** assert quantifier */
  void assertNode(Node q) override;

  std::string identify() const override;

  /** Get the state */
  State* getState();

 private:
  /** Add quantified formula to state */
  void addQuantToState(TNode q);
  /** State */
  State d_state;
  /** Instantiation driver */
  InstDriver d_driver;
  /** Term canonizer */
  expr::TermCanonize d_tcanon;
  /** The terms we have set up notifications for */
  NodeSet d_registeredTerms;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
