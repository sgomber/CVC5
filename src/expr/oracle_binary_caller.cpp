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

#include "expr/oracle_binary_caller.h"

#include <sstream>

#include "options/base_options.h"
#include "util/miniParser/miniParser.h"
#include "util/run.h"

namespace cvc5 {

std::vector<Term> OracleBinaryCaller::runOracle(const std::vector<Term>& input)
{
  std::vector<std::string> sargs;
  sargs.push_back(d_binaryName);

  Trace("oracle-calls") << "Call oracle " << input << std::endl;
  for (const Term& arg : input)
  {
    std::ostringstream oss;
    oss << arg;
    sargs.push_back(oss.str());
  }

  // Run the oracle binary for `sargs`, which indicates a list of
  // smt2 terms as strings.
  std::ostringstream stdout_stream;

  run(d_binaryName, sargs, "", stdout_stream, "");

  std::istringstream oracle_response_istream(stdout_stream.str());

  // Parse response from the binary into a Node. The response from the binary
  // should be a string that can be parsed as a (tuple of) terms in the smt2
  // format.
  internal::Node response =
      internal::mini_parsert(oracle_response_istream).expression();

  std::vector<Term> output = Term::nodeVectorToTerms(d_slv, {response});
  return output;
}

Term OracleBinaryCaller::runOracleSingleOut(const std::vector<Term>& input)
{
  // currently safe because the above assumes a single output
  std::vector<Term> output = runOracle(input);
  return output[0];
}

}  // namespace cvc5
