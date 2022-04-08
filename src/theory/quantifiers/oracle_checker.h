/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Elizabeth Polgreen
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Oracle checker, caches oracle caller objects
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__ORACLE_CHECKER_H
#define CVC5__THEORY__QUANTIFIERS__ORACLE_CHECKER_H

#include <vector>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "expr/oracle_caller.h"

namespace cvc5::internal {

class Env;

namespace theory {
namespace quantifiers {

/**
 * Oracle checker, maintains callers for all oracle functions.
 */
class OracleChecker : public NodeConverter
{
 public:
  OracleChecker(Env& env) : d_env(env) {}
  ~OracleChecker() {}

  /** check predicted ioPairs are consistent with oracles, generate lemmas if
   * not **/
  bool checkConsistent(const std::vector<std::pair<Node, Node> >& ioPairs,
                       std::vector<Node>& lemmas);
  /**
   * Evaluate an oracle application
   */
  Node evaluateApp(Node app);

  /** Evaluate all oracle function applications to constants */
  Node evaluate(Node n);

  /** Has oracles */
  bool hasOracles() const;
  /** Has oracle calls */
  bool hasOracleCalls(Node f) const;
  /** Get cached results */
  const std::map<Node, Node>& getOracleCalls(Node f) const;

 private:
  /** Call back to convert */
  Node postConvert(Node n) override;
  /** Reference to the env */
  Env& d_env;
  /** map of oracle interface nodes to oracle callers **/
  std::map<Node, OracleCaller> d_callers;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
