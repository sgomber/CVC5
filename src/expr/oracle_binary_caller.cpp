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

#include "parser/input_parser.h"
#include "util/run.h"

namespace cvc5 {

std::vector<Term> OracleBinaryCaller::runOracle(const std::vector<Term>& input)
{
  std::vector<std::string> sargs;
  sargs.push_back(d_binaryName);

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

  // initialize a new parser for the given solver and symbol manager
  parser::InputParser iparser(d_slv, d_sm, true);
  iparser.setStreamInput(d_slv->getOption("input-language"),
                         oracle_response_istream,
                         d_parseStreamName);
  // currently assumes a single output
  std::vector<Term> output;
  Term t = iparser.nextExpression();
  output.push_back(t);
  return output;
}

Term OracleBinaryCaller::runOracleSingleOut(const std::vector<Term>& input)
{
  // currently safe because the above assumes a single output
  std::vector<Term> output = runOracle(input);
  return output[0];
}

}  // namespace cvc5
