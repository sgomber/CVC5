/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common functions for dealing with nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__LINEAR_CONVERTER_H
#define CVC5__THEORY__ARITH__LINEAR_CONVERTER_H

#include "expr/node.h"
#include "smt/env_obj.h"
#include "expr/node_converter.h"

namespace cvc5::internal {

class Env;

namespace theory {
namespace arith {

/**
 * Convert to arith private, ensures rewritten.
 */
Node convertToArithPrivate(Env& env, TNode n);
/**
 * Convert from arith private, ensures rewritten.
 */
Node convertFromArithPrivate(Env& env, TNode n);
/**
 * Convert from arith private
 */
Node convertFromArithPrivate(TNode n);


class FromArithPrivateConverter : protected EnvObj, public NodeConverter
{
 public:
  FromArithPrivateConverter(Env& env);
  ~FromArithPrivateConverter() {}
  /** convert node n as described above during post-order traversal */
  Node postConvert(Node n) override;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__LINEAR_CONVERTER_H */
