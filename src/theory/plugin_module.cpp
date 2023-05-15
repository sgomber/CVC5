/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A theory engine module based on a user plugin.
 */

#include "theory/plugin_module.h"

namespace cvc5::internal {
namespace theory {

PluginModule::PluginModule(Env& env, TheoryEngine* theoryEngine, Plugin* p)
    : TheoryEngineModule(env, theoryEngine, "Plugin::" + p->getName()),
      d_plugin(p)
{
}

void PluginModule::check(Theory::Effort e)
{
  // ignore the effort level?
  std::vector<Node> lems = d_plugin->check();
  // returned vector is taken as lemmas
  for (const Node& lem : lems)
  {
    Assert(lem.getType().isBoolean());
    d_out.lemma(lem);
  }
}

}  // namespace theory
}  // namespace cvc5::internal
