/*********************                                                        */
/*! \file proof_db_pf.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof data structure for proof database
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__PROOF_DB_PF__H
#define CVC4__THEORY__PROOF_DB_PF__H

#include <string>
#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace theory {

enum ProofDbRuleId
{
  pf_rule_invalid,
  pf_rule_refl,
  pf_rule_eval,
  pf_rule_eq_refl,
  pf_rule_eq_sym,
  pf_rule_user
};

class ProofDbRule
{
 public:
  /** The name of the rule */
  std::string d_name;
  /** The conditions of the rule */
  std::vector<Node> d_cond;
  /** The conclusion of the rule (an equality) */
  Node d_eq;
  /** the ordered list of free variables */
  std::vector<Node> d_fvs;
  /** number of free variables */
  unsigned d_numFv;
  /**
   * The free variables that do not occur in the conditions. These cannot be
   * "holes" in a proof.
   */
  std::map<Node, bool> d_noOccVars;
  /** initialize this rule */
  void init(const std::string& name, const std::vector<Node>& cond, Node eq);
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__PROOF_DB_PF__H */
