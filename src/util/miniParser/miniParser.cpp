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

#include "miniParser.h"

#include <numeric>

#include "parser/parser_exception.h"
#include "util/bitvector.h"
#include "util/floatingpoint.h"
#include "util/rational.h"

namespace cvc5 {

inline bool has_prefix(const std::string& s, const std::string& prefix)
{
  return s.compare(0, prefix.size(), prefix) == 0;
}

tokenizert::tokent mini_parsert::next_token()
{
  const auto token = smt2_tokenizer.next_token();

  if (token == tokenizert::OPEN)
    parenthesis_level++;
  else if (token == tokenizert::CLOSE)
    parenthesis_level--;

  return token;
}

std::vector<Node> mini_parsert::operands()
{
  std::vector<Node> result;

  while (smt2_tokenizer.peek() != tokenizert::CLOSE)
    result.push_back(expression());

  next_token();  // eat the ')'

  return result;
}

Node mini_parsert::function_application(const Node& function,
                                        const std::vector<Node>& op)
{
  // check the arguments
  if (op.size() != function.getNumChildren())
    throw parser::ParserException("wrong number of arguments for function");

  NodeManager* nm = NodeManager::currentNM();
  Node fapp = nm->mkNode(kind::APPLY_UF, op);
  return fapp;
}

Node mini_parsert::expression()
{
  NodeManager* nm = NodeManager::currentNM();
  switch (next_token())
  {
    case tokenizert::SYMBOL:
    {
      const auto& identifier = smt2_tokenizer.get_buffer();

      // // in the expression table?
      const auto e_it = expressions.find(identifier);
      if (e_it != expressions.end()) return e_it->second();

      // if we want to parse symbols, this is where we look in the id map for
      // them

      // don't know, give up
      throw parser::ParserException("unknown expression " + identifier);
    }

    case tokenizert::NUMERAL:
    {
      const std::string& buffer = smt2_tokenizer.get_buffer();
      if (buffer.size() >= 2 && buffer[0] == '#' && buffer[1] == 'x')
      {
        Node result = nm->mkConst(
            BitVector(std::string(buffer, 2, std::string::npos), 16));
        return result;
      }
      else if (buffer.size() >= 2 && buffer[0] == '#' && buffer[1] == 'b')
      {
        Node result = nm->mkConst(
            BitVector(std::string(buffer, 2, std::string::npos), 2));
        return result;
      }
      else
      {
        Node result = nm->mkConstInt(Rational(buffer, 10));
        return result;
      }
    }

    case tokenizert::OPEN:  // function application
      return function_application();

    case tokenizert::END_OF_FILE:
      throw parser::ParserException("EOF in an expression");

    case tokenizert::CLOSE: CVC5_FALLTHROUGH;
    case tokenizert::STRING_LITERAL: CVC5_FALLTHROUGH;
    case tokenizert::NONE: CVC5_FALLTHROUGH;
    case tokenizert::KEYWORD:
      throw parser::ParserException("unexpected token in an expression");
  }

  Unhandled();
}

Node mini_parsert::function_application()
{
  NodeManager* nm = NodeManager::currentNM();
  switch (next_token())
  {
    case tokenizert::SYMBOL:
      if (smt2_tokenizer.get_buffer() == "_")  // indexed identifier
      {
        // indexed identifier
        if (next_token() != tokenizert::SYMBOL)
          throw parser::ParserException("expected symbol after '_'");

        // copy, the reference won't be stable
        const auto id = smt2_tokenizer.get_buffer();

        if (has_prefix(id, "bv"))
        {
          auto valString = smt2_tokenizer.get_buffer();

          if (next_token() != tokenizert::NUMERAL)
            throw parser::ParserException(
                "expected numeral as bitvector literal width");
          auto width = std::stoll(smt2_tokenizer.get_buffer());

          if (next_token() != tokenizert::CLOSE)
            throw parser::ParserException(
                "expected ')' after bitvector literal");

          Node result = nm->mkConst(BitVector(width, Integer(valString, 10)));
          return result;
        }
        else if (id == "+oo" || id == "-oo" || id == "NaN")
        {
          // These are the "plus infinity", "minus infinity" and NaN
          // floating-point literals.
          if (next_token() != tokenizert::NUMERAL)
            throw parser::ParserException("expected number after " + id);

          auto width_e = std::stoll(smt2_tokenizer.get_buffer());

          if (next_token() != tokenizert::NUMERAL)
            throw parser::ParserException("expected second number after " + id);

          auto width_f = std::stoll(smt2_tokenizer.get_buffer());

          if (next_token() != tokenizert::CLOSE)
            throw parser::ParserException("expected ')' after " + id);

          if (id == "+oo")
          {
            Node result = nm->mkConst(FloatingPoint::makeInf(
                FloatingPointSize(width_e, width_f), false));
            return result;
          }
          else if (id == "-oo")
          {
            Node result = nm->mkConst(FloatingPoint::makeInf(
                FloatingPointSize(width_e, width_f), true));
            return result;
          }
          else  // NaN
          {
            Node result = nm->mkConst(
                FloatingPoint::makeNaN(FloatingPointSize(width_e, width_f)));
            return result;
          }
        }
        else
        {
          // this includes things like rotate, extract, concat
          throw parser::ParserException("unknown indexed identifier " + id);
        }
      }
      else if (smt2_tokenizer.get_buffer() == "!")
      {
        throw parser::ParserException("Unable to parse attributes");
      }
      else
      {
        // non-indexed symbol, look up in expression table
        // non-indexed symbol, look up in expression table
        const auto id = smt2_tokenizer.get_buffer();
        const auto e_it = expressions.find(id);
        if (e_it != expressions.end()) return e_it->second();

        // // get the operands
        // auto op = operands();

        // // rummage through id_map
        // auto id_it = id_map.find(id);
        // if(id_it != id_map.end())
        // {
        //   if(id_it->second.type.id() == ID_mathematical_function)
        //   {
        //     return function_application(symbol_exprt(id, id_it->second.type),
        //     op);
        //   }
        //   else
        //     return symbol_exprt(id, id_it->second.type);
        // }
        else
          throw parser::ParserException("unknown function symbol " + id);
      }
      break;
    case tokenizert::OPEN:  // likely indexed identifier
      if (smt2_tokenizer.peek() == tokenizert::SYMBOL)
      {
        next_token();  // eat symbol
        if (smt2_tokenizer.get_buffer() == "_")
        {
          // indexed identifier
          if (next_token() != tokenizert::SYMBOL)
            throw parser::ParserException("expected symbol after '_'");

          std::string id = smt2_tokenizer.get_buffer();
          // this is where we would parse things like extract, rotate, extend
          if (id == "to_fp")
          {
            // this is where we parse to_fp
            throw parser::ParserException("We don't parse to_fp yet");
          }
          else
            throw parser::ParserException("Unable to parse indexed identifier");
        }
        else if (smt2_tokenizer.get_buffer() == "as")
        {
          // not parsed yet, but needed for arrays
          throw parser::ParserException("unexpected 'as' expression");
        }
        else
        {
          // just double parentheses
          Node tmp = expression();
          if (next_token() != tokenizert::CLOSE
              && next_token() != tokenizert::CLOSE)
          {
            throw parser::ParserException(
                "mismatched parentheses in an expression");
          }

          return tmp;
        }
      }
      else
      {
        // just double parentheses
        Node tmp = expression();

        if (next_token() != tokenizert::CLOSE
            && next_token() != tokenizert::CLOSE)
        {
          throw parser::ParserException(
              "mismatched parentheses in an expression");
        }

        return tmp;
      }
      break;

    case tokenizert::CLOSE:
    case tokenizert::NUMERAL:
    case tokenizert::STRING_LITERAL:
    case tokenizert::END_OF_FILE:
    case tokenizert::NONE:
    case tokenizert::KEYWORD:
      // just parentheses
      Node tmp = expression();
      if (next_token() != tokenizert::CLOSE)
        throw parser::ParserException(
            "mismatched parentheses in an expression");

      return tmp;
  }

  Unhandled();  // unreachable
}

// here we parse floats constructed with "(fp ...)"
// Node mini_parsert::function_application_fp(const std::vector<Node> &op)
// {
//   // return a floating point expression
// }

void mini_parsert::setup_expressions()
{
  // set up has table of expressions. We would put "fp" here
  expressions["true"] = [] {
    NodeManager* nm = NodeManager::currentNM();
    Node result = nm->mkConst(true);
    return result;
  };
  expressions["false"] = [] {
    NodeManager* nm = NodeManager::currentNM();
    Node result = nm->mkConst(false);
    return result;
  };
  // expressions["fp"] = [this] { return function_application_fp(operands()); };
}

};  // namespace cvc5
