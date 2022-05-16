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

#include "prop/lazy_prop_engine.h"

#include "prop/prop_engine.h"

namespace cvc5::internal {
namespace prop {

LazyPropEngine::LazyPropEngine(Env& env, PropEngine* pe) : EnvObj(env), d_propEngine(pe) {}

Result LazyPropEngine::checkSat(const std::vector<Node>& assertions,
                          std::unordered_map<size_t, Node>& skolemMap)
{
  // TODO
  d_propEngine->assertInputFormulas(assertions, skolemMap);
  return d_propEngine->checkSat();
}

}  // namespace prop
}  // namespace cvc5::internal

