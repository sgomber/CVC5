/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The lazy propositional engine
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__LAZY_PROP_ENGINE_H
#define CVC5__PROP__LAZY_PROP_ENGINE_H

#include "expr/node.h"
#include "smt/env_obj.h"
#include "util/result.h"

namespace cvc5::internal {
namespace prop {

class PropEngine;

/**
 * PropEngine is the abstraction of a Sat Solver, providing methods for
 * solving the SAT problem and conversion to CNF (via the CnfStream).
 */
class LazyPropEngine : protected EnvObj
{
 public:
  /**
   * Create a LazyPropEngine with a particular prop engine.
   */
  LazyPropEngine(Env& env, PropEngine* pe);
  /**Destructor.*/
  ~LazyPropEngine() {}
  /**
   * Check sat
   */
  Result checkSat(const std::vector<Node>& assertions,
                           std::unordered_map<size_t, Node>& skolemMap);
 private:
  /** The prop engine we will be using */
  PropEngine* d_propEngine;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__LAZY_PROP_ENGINE_H */
