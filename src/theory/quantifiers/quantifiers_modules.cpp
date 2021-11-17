/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Class for initializing the modules of quantifiers engine.
 */

#include "theory/quantifiers/quantifiers_modules.h"

#include "options/quantifiers_options.h"
#include "options/strings_options.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/term_registry.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

QuantifiersModules::QuantifiersModules()
    : d_rel_dom(nullptr),
      d_alpha_equiv(nullptr),
      d_inst_engine(nullptr),
      d_model_engine(nullptr),
      d_bint(nullptr),
      d_qcf(nullptr),
      d_sg_gen(nullptr),
      d_synth_e(nullptr),
      d_fs(nullptr),
      d_ipool(nullptr),
      d_i_cbqi(nullptr),
      d_qsplit(nullptr),
      d_sygus_inst(nullptr)
{
}
QuantifiersModules::~QuantifiersModules() {}
void QuantifiersModules::initialize(Env& env,
                                    QuantifiersState& qs,
                                    QuantifiersInferenceManager& qim,
                                    QuantifiersRegistry& qr,
                                    TermRegistry& tr,
                                    QModelBuilder* builder,
                                    std::vector<QuantifiersModule*>& modules)
{
  const Options& opts = env.getOptions();
  // add quantifiers modules
  if (opts.quantifiers.ccfv)
  {
    d_ccfv.reset(new ccfv::CongruenceClosureFv(env, qs, qim, qr, tr));
    modules.push_back(d_ccfv.get());
  }
  if (opts.quantifiers.quantConflictFind)
  {
    d_qcf.reset(new QuantConflictFind(env, qs, qim, qr, tr));
    modules.push_back(d_qcf.get());
  }
  if (opts.quantifiers.conjectureGen)
  {
    d_sg_gen.reset(new ConjectureGenerator(env, qs, qim, qr, tr));
    modules.push_back(d_sg_gen.get());
  }
  if (!opts.quantifiers.finiteModelFind || opts.quantifiers.fmfInstEngine)
  {
    d_inst_engine.reset(new InstantiationEngine(env, qs, qim, qr, tr));
    modules.push_back(d_inst_engine.get());
  }
  if (opts.quantifiers.cegqi)
  {
    d_i_cbqi.reset(new InstStrategyCegqi(env, qs, qim, qr, tr));
    modules.push_back(d_i_cbqi.get());
    qim.getInstantiate()->addRewriter(d_i_cbqi->getInstRewriter());
  }
  if (opts.quantifiers.sygus)
  {
    d_synth_e.reset(new SynthEngine(env, qs, qim, qr, tr));
    modules.push_back(d_synth_e.get());
  }
  // bounded integer instantiation is used when the user requests it via
  // fmfBound, or if strings are enabled.
  if (opts.quantifiers.fmfBound || opts.strings.stringExp)
  {
    d_bint.reset(new BoundedIntegers(env, qs, qim, qr, tr));
    modules.push_back(d_bint.get());
  }

  if (opts.quantifiers.finiteModelFind || opts.quantifiers.fmfBound
      || opts.strings.stringExp)
  {
    d_model_engine.reset(new ModelEngine(env, qs, qim, qr, tr, builder));
    modules.push_back(d_model_engine.get());
  }
  if (opts.quantifiers.quantDynamicSplit != options::QuantDSplitMode::NONE)
  {
    d_qsplit.reset(new QuantDSplit(env, qs, qim, qr, tr));
    modules.push_back(d_qsplit.get());
  }
  if (opts.quantifiers.quantAlphaEquiv)
  {
    d_alpha_equiv.reset(new AlphaEquivalence(env));
  }
  // full saturation : instantiate from relevant domain, then arbitrary terms
  if (opts.quantifiers.fullSaturateQuant
      || opts.quantifiers.fullSaturateInterleave)
  {
    d_rel_dom.reset(new RelevantDomain(env, qs, qr, tr));
    d_fs.reset(new InstStrategyEnum(env, qs, qim, qr, tr, d_rel_dom.get()));
    modules.push_back(d_fs.get());
  }
  if (opts.quantifiers.poolInst)
  {
    d_ipool.reset(new InstStrategyPool(env, qs, qim, qr, tr));
    modules.push_back(d_ipool.get());
  }
  if (opts.quantifiers.sygusInst)
  {
    d_sygus_inst.reset(new SygusInst(env, qs, qim, qr, tr));
    modules.push_back(d_sygus_inst.get());
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
