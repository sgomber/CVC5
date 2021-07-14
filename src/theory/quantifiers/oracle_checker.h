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
#include "util/oracle_caller.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

/**
 * Oracle checker
 */
class OracleChecker
{
 public:
  OracleChecker() {}
  ~OracleChecker() {}

  /** check predicted ioPairs are consistent with oracles, generate lemmas if
   * not **/
  bool checkConsistent(const std::vector<std::pair<Node, Node> >& ioPairs,
                       std::vector<Node>& lemmas);

 private:
  /** map of oracle interface nodes to oracle callers **/
  std::map<Node, OracleCaller> d_callers;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
