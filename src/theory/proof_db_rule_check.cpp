/*********************                                                        */
/*! \file proof_db_rule_check.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of Proof db rule check.
 **/

#include "theory/proof_db_rule_check.h"

#include "expr/node_algorithm.h"
#include "theory/proof_db_sc.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

void ProofDbRuleCheck::quickCheckRules(const std::map<Node, std::string>& rules)
{
  // needed?
  std::stringstream out;
  for (const std::pair<const Node, std::string>& rr : rules)
  {
    Trace("proof-db-check") << "ProofDbRuleCheck:: Check rule " << rr.second << "..." << std::endl;
    if (addTerm(rr.first,out)) 
    {
      Trace("proof-db-check") << "ProofDbRuleCheck:: ...unsound!!!!" << std::endl;
    }
  }
}

bool ProofDbRuleCheck::addTerm(Node n, std::ostream& out)
{
  // does it have side conditions?
  if( ProofDbScEval::hasSideCondition(n))
  {
    Trace("proof-db-check") << "ProofDbRuleCheck:: ...SKIP (has side condition)" << std::endl;
    return false;
  }
  Node nr = Rewriter::rewrite(n.negate());
  
  // any unhandled features, e.g. regular expression variables
  std::unordered_set< Node, NodeHashFunction > fvs;
  expr::getFreeVariables(nr,fvs);
  for( const Node& v : fvs )
  {
    if( v.getType().isRegExp() )
    {
      Trace("proof-db-check") << "ProofDbRuleCheck:: ...SKIP (has regular expression variable)" << std::endl;
      return false;
    }
  }
  
  if( nr.isConst() && !nr.getConst<bool>() )
  {
    Trace("proof-db-check") << "ProofDbRuleCheck:: ...SUCCESS (trivial)" << std::endl;
    return false;
  }
  Result r = doCheck(nr);
  if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    Trace("proof-db-check") << "ProofDbRuleCheck:: ...SUCCESS" << std::endl;
    return false;
  }
  Trace("proof-db-check") << "ProofDbRuleCheck:: ...FAIL (query returned " << r << ")" << std::endl;
  return true;
}

}  // namespace theory
}  // namespace CVC4
