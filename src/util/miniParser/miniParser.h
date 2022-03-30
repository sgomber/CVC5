/******************************************************************************
 * Top contributors (to current version):
 *   Elizabeth Polgreen
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Mini parser used for parsing back oracle responses
 */
#ifndef CVC5__UTIL__MINIPARSER_MINIPARSER_H
#define CVC5__UTIL__MINIPARSER_MINIPARSER_H

#include <functional>
#include <map>
#include <set>
#include <unordered_map>

#include "cvc5_private.h"
#include "expr/node.h"
#include "tokenizer.h"

namespace cvc5::internal {

class mini_parsert
{
 public:
  explicit mini_parsert(std::istream& _in)
      : exit(false), smt2_tokenizer(_in), parenthesis_level(0)
  {
    setup_expressions();
  }

  Node expression();
  bool exit;

 protected:
  tokenizert smt2_tokenizer;
  // we extend next_token to track the parenthesis level
  std::size_t parenthesis_level;
  tokenizert::tokent next_token();

  // // hashtable for all expressions
  std::unordered_map<std::string, std::function<Node()>> expressions;
  void setup_expressions();

  std::vector<Node> operands();
  Node function_application(const Node& function, const std::vector<Node>& op);
  Node function_application();

  // kind::Kind_t parse_rounding_mode(const std::string &mode_string);
  // Node function_application_fp(std::vector<Node> ops);
};

}  // namespace cvc5::internal
#endif  // CVC5__UTIL__MINIPARSER_MINIPARSER_H
