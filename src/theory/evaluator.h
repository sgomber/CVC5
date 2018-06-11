/*********************                                                        */
/*! \file evaluator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The Evaluator class
 **
 ** The Evaluator class.
 **/

#include "cvc4_private.h"

#pragma once

#include <utility>
#include <vector>

#include "base/output.h"
#include "expr/node.h"
#include "util/bitvector.h"

namespace CVC4 {
namespace theory {

struct Result
{
  enum
  {
    BITVECTOR,
    BOOL,
    INVALID
  } d_tag;
  union
  {
    bool d_bool;
    BitVector d_bv;
  };

  Result(const Result& other)
  {
    d_tag = other.d_tag;
    switch (d_tag)
    {
      case BITVECTOR:
        new (&d_bv) BitVector;
        d_bv = other.d_bv;
        break;
      case BOOL: d_bool = other.d_bool; break;
      case INVALID: break;
    }
  }

  Result() : d_tag(INVALID) {}

  Result(bool b) : d_tag(BOOL), d_bool(b) {}

  Result(const BitVector& bv) : d_tag(BITVECTOR), d_bv(bv) {}

  Result& operator=(const Result& other)
  {
    if (this != &other)
    {
      d_tag = other.d_tag;
      switch (d_tag)
      {
        case BITVECTOR:
          new (&d_bv) BitVector;
          d_bv = other.d_bv;
          break;
        case BOOL: d_bool = other.d_bool; break;
        case INVALID: break;
      }
    }
    return *this;
  }

  ~Result()
  {
    if (d_tag == BITVECTOR)
    {
      d_bv.~BitVector();
    }
  }

  Node toNode()
  {
    NodeManager* nm = NodeManager::currentNM();
    switch (d_tag)
    {
      case Result::BITVECTOR: return nm->mkConst(d_bv);
      case Result::BOOL: return nm->mkConst(d_bool);
      default:
      {
        Trace("evaluator") << "Missing conversion from " << d_tag << " to node"
                           << std::endl;
        return Node();
      }
    }

    return Node();
  }
};

class Evaluator
{
 public:
  Node eval(TNode n,
            const std::vector<Node>& args,
            const std::vector<Node>& vals);

 private:
  bool d_hasResult;
  std::unordered_map<TNode, Result, TNodeHashFunction> d_results;
};

}  // namespace theory
}  // namespace CVC4
