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
 * Oracle caller
 */

#include "cvc5_private.h"

#ifndef CVC5__UTIL__ORACLE_CALLER_H
#define CVC5__UTIL__ORACLE_CALLER_H

#include "expr/node.h"

namespace cvc5 {

class OracleCaller
{
 public:
  /** functions for minimal parsing. These will be removed */
  Node get_hex_numeral(std::string in);
  Node get_dec_numeral(std::string in);
  Node get_bin_numeral(std::string in);
  Node responseParser(std::string &in);

  /** Call an oracle with a set of arguments **/
  Node callOracle(const std::string &binName, 
                         const std::vector<Node> &argv);

  /** get binary from oracle interface */
  std::string getBinaryName(const Node n);

};

} // namespace cvc5

#endif /*CVC5__UTIL__ORACLE_CALLER_H*/