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
 * tokenizer for mini parser used for parsing back oracle responses
 */
#ifndef CVC5__UTIL__MINIPARSER_TOKENIZER_H
#define CVC5__UTIL__MINIPARSER_TOKENIZER_H

#include <sstream>
#include <string>

#include "base/exception.h"

namespace cvc5::internal {

class tokenizert
{
 public:
  explicit tokenizert(std::istream& _in) : peeked(false), token(NONE)
  {
    in = &_in;
    line_no = 1;
  }

  using tokent = enum {
    NONE,
    END_OF_FILE,
    STRING_LITERAL,
    NUMERAL,
    SYMBOL,
    KEYWORD,
    OPEN,
    CLOSE
  };

  tokent next_token();

  tokent peek()
  {
    if (peeked)
      return token;
    else
    {
      get_token_from_stream();
      peeked = true;
      return token;
    }
  }

  const std::string& get_buffer() const { return buffer; }

  bool token_is_quoted_symbol() const { return quoted_symbol; }

 protected:
  std::istream* in;
  unsigned line_no;
  std::string buffer;
  bool quoted_symbol = false;
  bool peeked;
  tokent token;

  /// skip any tokens until all parentheses are closed
  /// or the end of file is reached
  void skip_to_end_of_list();

 private:
  tokent get_decimal_numeral();
  tokent get_hex_numeral();
  tokent get_bin_numeral();
  tokent get_simple_symbol();
  tokent get_quoted_symbol();
  tokent get_string_literal();
  static bool is_simple_symbol_character(char);

  /// read a token from the input stream and store it in 'token'
  void get_token_from_stream();
};

}  // namespace cvc5::internal

#endif  // CVC5__UTIL__MINIPARSER_TOKENIZER_H
