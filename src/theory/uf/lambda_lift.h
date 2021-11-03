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
 * Lambda lifting
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__UF__LAMBDA_LIFT_H
#define CVC5__THEORY__UF__LAMBDA_LIFT_H

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5 {
namespace theory {
namespace uf {

/**
 */
class LambdaLift : protected EnvObj
{
 public:
  LambdaLift(Env& env);

  /** process */
  void process(Node node);
 private:
  /** Get assertion for */
  static Node getAssertionFor(TNode node);
  /** Get skolem for */
  static Node getSkolemFor(TNode node);
};

}  // namespace uf
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__UF__LAMBDA_LIFT_H */
