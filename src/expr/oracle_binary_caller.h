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

#ifndef CVC5__EXPR__ORACLE_BINARY_CALLER_H
#define CVC5__EXPR__ORACLE_BINARY_CALLER_H

#include "expr/node.h"
#include "expr/node_trie.h"

namespace cvc5::internal {

//!!!!!!!!!!!! TEMPORARY
class OracleBinaryCaller
{
 public:
  OracleBinaryCaller(std::string binName) : d_binaryName(binName) {}
  /** Run */
  std::vector<Node> runOracle(const std::vector<Node>& input);

 private:
  /** binary name */
  std::string d_binaryName;
};

}  // namespace cvc5::internal

#endif /*CVC5__UTIL__ORACLE_CALLER_H*/
