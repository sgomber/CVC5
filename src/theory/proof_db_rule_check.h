/*********************                                                        */
/*! \file proof_db_rule_check.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof database
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__PROOF_DB_RULE_CHECK__H
#define CVC4__THEORY__PROOF_DB_RULE_CHECK__H

#include <map>
#include <string>
#include "expr/node.h"
#include "theory/quantifiers/expr_miner.h"

namespace CVC4 {
namespace theory {

/** ProofDb
 */
class ProofDbRuleCheck : public quantifiers::ExprMiner
{
 public:
  ProofDbRuleCheck(){}
  /**
   * Quick check rules
   */
  void quickCheckRules(const std::map<Node, std::string>& rules);
  
  /** returns true if an unsoundness detected */
  bool addTerm(Node n, std::ostream& out) override;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__PROOF_DB_RULE_CHECK__H */
