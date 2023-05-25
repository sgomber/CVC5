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

#include "smt/env.h"
#include "theory/trust_substitutions.h"

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
    // must apply top level substitutions here, since if this lemma was
    // sent externally, it may not have taken into account the internal
    // substitutions.
    Node slem = d_env.getTopLevelSubstitutions().apply(lem);
    // send the lemma
    d_out.lemma(slem);
  }
}

void PluginModule::notifyLemma(TNode n,
                               theory::LemmaProperty p,
                               const std::vector<Node>& skAsserts,
                               const std::vector<Node>& sks)
{
  Trace("ajr-temp") << "Plugin notify " << n << std::endl;
  // currently ignores the other fields
  d_plugin->notifyLemma(n);
  // skolem lemmas
  for (const Node& kn : skAsserts)
  {
    d_plugin->notifyLemma(kn);
  }
}

}  // namespace theory
}  // namespace cvc5::internal
