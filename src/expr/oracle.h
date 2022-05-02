/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
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

#ifndef CVC5__EXPR__ORACLE_H
#define CVC5__EXPR__ORACLE_H

#include <vector>

#include "expr/node.h"

namespace cvc5::internal {

/**
 * An oracle, which stores a function.
 */
class Oracle
{
 public:
  /**
   */
  Oracle(std::function<std::vector<Node>(const std::vector<Node>&)> fn)
      : d_fn(fn)
  {
  }

  ~Oracle() {}

  /** Get the function for this oracle */
  std::function<std::vector<Node>(const std::vector<Node>&)> getFunction() const
  {
    return d_fn;
  }

 private:
  /** The function for this oracle */
  std::function<std::vector<Node>(const std::vector<Node>&)> d_fn;
};

}  // namespace cvc5::internal

#endif /*CVC5__EXPR__ORACLE_H*/
