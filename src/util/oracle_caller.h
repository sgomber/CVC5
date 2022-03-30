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
#include "expr/node_trie.h"

namespace cvc5::internal {

class OracleCaller
{
 public:
  OracleCaller(const Node oracleInterfaceNode)
      : d_binaryName(getBinaryNameFor(oracleInterfaceNode)){};

  ~OracleCaller() {}
  /** functions for minimal parsing. These will be removed */
  Node get_hex_numeral(std::string in);
  Node get_dec_numeral(std::string in);
  Node get_bin_numeral(std::string in);
  Node responseParser(std::string& in);

  /**
   * Call an oracle with a set of arguments, store in result res.
   *
   * Return true if the call was made, and false if it was already cached.
   *
   * If this method returns true, then runResult is set to the result returned
   * from executing the binary.
   */
  bool callOracle(Node fapp, Node& res, int& runResult);

  /** get binary from oracle interface */
  static std::string getBinaryNameFor(const Node n);

  /** get binary from oracle interface */
  std::string getBinaryName() { return d_binaryName; }

  /** is f an oracle function? */
  static bool isOracleFunction(Node f);

  /** get cached results */
  const std::map<Node, Node>& getCachedResults() const;

 private:
  /** name of binary */
  std::string d_binaryName;
  std::map<Node, Node> d_cachedResults;
};

}  // namespace cvc5::internal

#endif /*CVC5__UTIL__ORACLE_CALLER_H*/
