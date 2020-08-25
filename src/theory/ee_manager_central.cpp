/*********************                                                        */
/*! \file ee_manager_central.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for equality sharing.
 **/

#include "theory/ee_manager_central.h"

#include "theory/quantifiers_engine.h"
#include "theory/shared_solver.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

EqEngineManagerCentral::EqEngineManagerCentral(TheoryEngine& te, SharedSolver& shs)
    : EqEngineManager(te, shs),
      d_centralEENotify(*this),
      // we do not require any term triggers in the central equality engine
      d_centralEqualityEngine(
          d_centralEENotify, te.getSatContext(), "centralEE", false, false),
      d_buildingModel(te.getSatContext(), false)
{
  for (TheoryId theoryId = theory::THEORY_FIRST;
       theoryId != theory::THEORY_LAST;
       ++theoryId)
  {
    d_theoryNotify[theoryId] = nullptr;
  }
}

EqEngineManagerCentral::~EqEngineManagerCentral() {}

void EqEngineManagerCentral::initializeTheories()
{
  Trace("eem-central") << "EqEngineManagerCentral::initializeTheories"
                       << std::endl;
  // set the shared solver's equality engine to central
  d_sharedSolver.setEqualityEngine(&d_centralEqualityEngine);
  // allocate equality engines per theory
  for (TheoryId theoryId = theory::THEORY_FIRST;
       theoryId != theory::THEORY_LAST;
       ++theoryId)
  {
    Theory* t = d_te.theoryOf(theoryId);
    if (t == nullptr)
    {
      // theory not active, skip
      continue;
    }
    // always allocate an object in d_einfo here
    EeTheoryInfo& eet = d_einfo[theoryId];
    EeSetupInfo esi;
    if (!t->needsEqualityEngine(esi))
    {
      // theory said it doesn't need an equality engine, skip
      continue;
    }
    // set the notification class
    eq::EqualityEngineNotify* notify = esi.d_notify;
    d_theoryNotify[theoryId] = notify;
    // add to vectors for the kinds of notifications
    if (esi.needsNotifyNewEqClass())
    {
      d_centralEENotify.d_newClassNotify.push_back(notify);
    }
    if (esi.needsNotifyMerge())
    {
      d_centralEENotify.d_mergeNotify.push_back(notify);
    }
    if (esi.needsNotifyDisequal())
    {
      d_centralEENotify.d_disequalNotify.push_back(notify);
    }
    // the theory uses the central equality engine
    eet.d_usedEe = &d_centralEqualityEngine;
  }

  // also take pointer to quantifiers engine
  const LogicInfo& logicInfo = d_te.getLogicInfo();
  if (logicInfo.isQuantified())
  {
    d_centralEENotify.d_quantEngine = d_te.getQuantifiersEngine();
  }
}

eq::EqualityEngine* EqEngineManagerCentral::getCoreEqualityEngine()
{
  return &d_centralEqualityEngine;
}

EqEngineManagerCentral::CentralNotifyClass::CentralNotifyClass(
    EqEngineManagerCentral& eemc)
    : d_eemc(eemc), d_mNotify(nullptr), d_quantEngine(nullptr)
{
}

bool EqEngineManagerCentral::CentralNotifyClass::eqNotifyTriggerPredicate(
    TNode predicate, bool value)
{
  Trace("eem-central") << "eqNotifyTriggerPredicate: " << predicate
                       << std::endl;
  return d_eemc.eqNotifyTriggerPredicate(predicate, value);
}

bool EqEngineManagerCentral::CentralNotifyClass::eqNotifyTriggerTermEquality(
    TheoryId tag, TNode t1, TNode t2, bool value)
{
  Unreachable() << "EqEngineManagerCentral::eqNotifyTriggerTermEquality: no "
                   "need to propagate equalities between shared terms";
}

void EqEngineManagerCentral::CentralNotifyClass::eqNotifyConstantTermMerge(
    TNode t1, TNode t2)
{
  Trace("eem-central") << "eqNotifyConstantTermMerge: " << t1 << " " << t2
                       << std::endl;
  d_eemc.eqNotifyConstantTermMerge(t1, t2);
}

void EqEngineManagerCentral::CentralNotifyClass::eqNotifyNewClass(TNode t)
{
  Trace("eem-central") << "...eqNotifyNewClass " << t << std::endl;
  // notify all theories that have new equivalence class notifications
  for (eq::EqualityEngineNotify* notify : d_newClassNotify)
  {
    notify->eqNotifyNewClass(t);
  }
  // also always forward to quantifiers
  if (d_quantEngine != nullptr)
  {
    d_quantEngine->eqNotifyNewClass(t);
  }
}

void EqEngineManagerCentral::CentralNotifyClass::eqNotifyMerge(TNode t1,
                                                               TNode t2)
{
  Trace("eem-central") << "...eqNotifyMerge " << t1 << ", " << t2 << std::endl;
  // notify all theories that have merge notifications
  for (eq::EqualityEngineNotify* notify : d_mergeNotify)
  {
    notify->eqNotifyMerge(t1, t2);
  }
}

void EqEngineManagerCentral::CentralNotifyClass::eqNotifyDisequal(TNode t1,
                                                                  TNode t2,
                                                                  TNode reason)
{
  Trace("eem-central") << "...eqNotifyDisequal " << t1 << ", " << t2
                       << std::endl;
  // notify all theories that have disequal notifications
  for (eq::EqualityEngineNotify* notify : d_disequalNotify)
  {
    notify->eqNotifyDisequal(t1, t2, reason);
  }
}

bool EqEngineManagerCentral::eqNotifyTriggerPredicate(TNode predicate,
                                                      bool value)
{
  // if we're building model, ignore this propagation
  if (d_buildingModel.get())
  {
    return true;
  }
  Theory* t = d_te.getActiveTheory();
  if (t==nullptr)
  {
    // TODO: shared solver?
  }
  TheoryId tid = t == nullptr ? THEORY_BUILTIN : t->getId();
  Trace("eem-central") << "...propagate " << predicate << ", " << value
                       << " with " << tid << std::endl;
  // propagate directly to theory engine
  if (value)
  {
    return d_te.propagate(predicate, tid);
  }
  return d_te.propagate(predicate.notNode(), tid);
}

void EqEngineManagerCentral::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  Theory* t = d_te.getActiveTheory();
  if (t == nullptr)
  {
    // probably in shared solver?
    Node lit = t1.eqNode(t2);
    Node conflict = d_centralEqualityEngine.mkExplainLit(lit);
    d_te.conflict(conflict, THEORY_BUILTIN);
    return;
  }
  Trace("eem-central") << "...notify active theory " << t->getId() << std::endl;
  eq::EqualityEngineNotify* notify = d_theoryNotify[t->getId()];
  Assert(notify != nullptr);
  notify->eqNotifyConstantTermMerge(t1, t2);
}

void EqEngineManagerCentral::notifyBuildingModel()
{
  // disable theory notifications in this context
}

}  // namespace theory
}  // namespace CVC4
