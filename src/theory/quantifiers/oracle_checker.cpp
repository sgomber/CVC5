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
 * Oracle checker
 */

#include "theory/quantifiers/oracle_checker.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

bool OracleChecker::checkConsistent(
    const std::vector<std::pair<Node, Node> >& ioPairs,
    std::vector<Node>& lemmas)
{
  bool consistent = true;
  NodeManager* nm = NodeManager::currentNM();
  for (const auto& ioPair : ioPairs)
  {
    Node result = evaluate(ioPair.first);
    if (result != ioPair.second)
    {
      Node lemma = nm->mkNode(kind::EQUAL, result, ioPair.first);
      lemmas.push_back(lemma);
      consistent = false;
    }
  }
  return consistent;
}

Node OracleChecker::evaluate(Node app)
{
  Assert (app.getKind()==APPLY_UF);
  Node f = app.getOperator();
  Assert (OracleCaller::isOracleFunction(f));
  // get oracle caller
  if (d_callers.find(f) == d_callers.end())
  {
    d_callers.insert(std::pair<Node, OracleCaller>(f, OracleCaller(f)));
  }
  OracleCaller& caller = d_callers.at(f);
  // get oracle result
  return caller.callOracle(app);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
