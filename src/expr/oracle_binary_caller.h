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

#include "cvc5_public.h"

#ifndef CVC5__EXPR__ORACLE_BINARY_CALLER_H
#define CVC5__EXPR__ORACLE_BINARY_CALLER_H

#include "api/cpp/cvc5.h"

namespace cvc5 {

//!!!!!!!!!!!! TEMPORARY
class OracleBinaryCaller
{
 public:
  OracleBinaryCaller(Solver* slv, std::string binName)
      : d_slv(slv), d_binaryName(binName)
  {
  }
  /** Run */
  std::vector<Term> runOracle(const std::vector<Term>& input);

 private:
  /** pointer to solver */
  Solver* d_slv;
  /** binary name */
  std::string d_binaryName;
};

}  // namespace cvc5

#endif /*CVC5__UTIL__ORACLE_CALLER_H*/
