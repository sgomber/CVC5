/*********************                                                        */
/*! \file ee_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for management of equality engines.
 **/

#include "theory/ee_manager.h"

#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {

EqEngineManager::EqEngineManager() : d_modelEqualityEngine(nullptr) {}

void EqEngineManager::initializeModel(TheoryModel* m,
                                      eq::EqualityEngineNotify* notify,
                                      context::Context* c)
{
#if 0
  Assert(m != nullptr);
  // set the notification class
  d_centralEENotify.d_mNotify = notify;
  // model uses the central equality engine, finish initialize
  m->finishInit(&d_centralEqualityEngine);
#endif
  Assert(m != nullptr);
  // initialize the model equality engine, use the provided notification object,
  // which belongs e.g. to CombinationModelBased
  EeSetupInfo esim;
  esim.d_notify = notify;
  d_modelEqualityEngineAlloc.reset(allocateEqualityEngine(esim, c));
  d_modelEqualityEngine = d_modelEqualityEngineAlloc.get();
  m->finishInit(d_modelEqualityEngine);
  // FIXME
  c->push();
}

const EeTheoryInfo* EqEngineManager::getEeTheoryInfo(TheoryId tid) const
{
  std::map<TheoryId, EeTheoryInfo>::const_iterator it = d_einfo.find(tid);
  if (it != d_einfo.end())
  {
    return &it->second;
  }
  return nullptr;
}

eq::EqualityEngine* EqEngineManager::getModelEqualityEngine()
{
  return d_modelEqualityEngine;
}

const std::unordered_set<Node, NodeHashFunction>&
EqEngineManager::getEqcRepresentatives() const
{
  return d_eqCache->get();
}

const std::vector<Node>& EqEngineManager::getEqcRepresentativesForType(
    TypeNode t) const
{
  return d_eqCache->getForType(t);
}

void EqEngineManager::addFunctionKinds(eq::EqualityEngine* ee, EeSetupInfo& esi)
{
  for (const EeSetupFunctionKind& esf : esi.d_functionKinds)
  {
    ee->addFunctionKind(esf.d_kind, esf.d_isInterpreted, esf.d_isExtOperator);
  }
}

eq::EqualityEngine* EqEngineManager::allocateEqualityEngine(EeSetupInfo& esi,
                                                            context::Context* c)
{
  if (esi.d_notify != nullptr)
  {
    return new eq::EqualityEngine(
        *esi.d_notify, c, esi.d_name, esi.d_constantsAreTriggers);
  }
  // the theory doesn't care about explicit notifications
  return new eq::EqualityEngine(c, esi.d_name, esi.d_constantsAreTriggers);
}

}  // namespace theory
}  // namespace CVC4
