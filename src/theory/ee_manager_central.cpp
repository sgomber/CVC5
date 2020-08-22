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
#include "theory/shared_terms_database.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

EqEngineManagerCentral::EqEngineManagerCentral(TheoryEngine& te)
    : d_te(te),
      d_centralEENotify(),
      // we do not require any term triggers in the central equality engine
      d_centralEqualityEngine(
          d_centralEENotify, te.getSatContext(), "centralEE", false, false)
{
}

EqEngineManagerCentral::~EqEngineManagerCentral() {}

void EqEngineManagerCentral::initializeTheories(SharedSolver* sharedSolver)
{
  // set the shared solver's equality engine
  sharedSolver->setEqualityEngine(&d_centralEqualityEngine);
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
    d_centralEENotify.d_theoryNotify[theoryId] = notify;
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

void EqEngineManagerCentral::initializeModel(TheoryModel* m)
{
  Assert(m != nullptr);
  // initialize the model equality engine
  EeSetupInfo esim;
  if (m->needsEqualityEngine(esim))
  {
    // set the notification class
    d_centralEENotify.d_mNotify = esim.d_notify;
    // model uses the central equality engine
    m->setEqualityEngine(&d_centralEqualityEngine);
  }
  else
  {
    AlwaysAssert(false) << "Expected model to use equality engine";
  }
  m->finishInit();
}

eq::EqualityEngine* EqEngineManagerCentral::getCoreEqualityEngine()
{
  return &d_centralEqualityEngine;
}

EqEngineManagerCentral::CentralNotifyClass::CentralNotifyClass()
    : d_sdbNotify(nullptr), d_mNotify(nullptr), d_quantEngine(nullptr)
{
  for (TheoryId theoryId = theory::THEORY_FIRST;
       theoryId != theory::THEORY_LAST;
       ++theoryId)
  {
    d_theoryNotify[theoryId] = nullptr;
  }
}
void EqEngineManagerCentral::CentralNotifyClass::eqNotifyNewClass(TNode t)
{
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

bool EqEngineManagerCentral::CentralNotifyClass::eqNotifyTriggerPredicate(
    TNode predicate, bool value)
{
  /*
  if (value) {
    return d_uf.propagate(predicate);
  } else {
    return d_uf.propagate(predicate.notNode());
  }
  */
  TheoryId tid = Theory::theoryOf(predicate);
  Assert(d_theoryNotify[tid] != nullptr);
  return d_theoryNotify[tid]->eqNotifyTriggerPredicate(predicate, value);
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
  /*
  d_uf.conflict(t1, t2);
  */
  TheoryId tid = Theory::theoryOf(t1.getType());
  Assert(d_theoryNotify[tid] != nullptr);
  d_theoryNotify[tid]->eqNotifyConstantTermMerge(t1, t2);
}

void EqEngineManagerCentral::CentralNotifyClass::eqNotifyMerge(TNode t1,
                                                               TNode t2)
{
  for (eq::EqualityEngineNotify* notify : d_mergeNotify)
  {
    notify->eqNotifyMerge(t1, t2);
  }
}

void EqEngineManagerCentral::CentralNotifyClass::eqNotifyDisequal(TNode t1,
                                                                  TNode t2,
                                                                  TNode reason)
{
  for (eq::EqualityEngineNotify* notify : d_disequalNotify)
  {
    notify->eqNotifyDisequal(t1, t2, reason);
  }
}

}  // namespace theory
}  // namespace CVC4
