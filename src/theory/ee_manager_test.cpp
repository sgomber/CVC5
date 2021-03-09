/*********************                                                        */
/*! \file ee_manager_test.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a test approach for equality sharing.
 **/

#include "theory/ee_manager_test.h"

#include "theory/quantifiers_engine.h"
#include "theory/shared_solver.h"
#include "theory/theory_engine.h"
#include "theory/theory_state.h"

namespace CVC4 {
namespace theory {

EqEngineManagerTest::EqEngineManagerTest(TheoryEngine& te, SharedSolver& shs)
    : EqEngineManager(te, shs),
      d_masterEENotify(nullptr),
      d_centralEENotify(*this),
      d_centralEqualityEngine(
          d_centralEENotify, te.getSatContext(), "centralEE", true),
      d_buildingModel(te.getSatContext(), false)
{
  for (TheoryId theoryId = theory::THEORY_FIRST;
       theoryId != theory::THEORY_LAST;
       ++theoryId)
  {
    d_theoryNotify[theoryId] = nullptr;
  }
}

EqEngineManagerTest::~EqEngineManagerTest() {}

void EqEngineManagerTest::initializeTheories()
{
  context::Context* c = d_te.getSatContext();
  // initialize the shared solver
  EeSetupInfo esis;
  if (d_sharedSolver.needsEqualityEngine(esis))
  {
    // use central equality engine
    d_sharedSolver.setEqualityEngine(&d_centralEqualityEngine);
  }
  else
  {
    AlwaysAssert(false) << "Expected shared solver to use equality engine";
  }

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
    // set the notify
    eq::EqualityEngineNotify* notify = esi.d_notify;
    d_theoryNotify[theoryId] = notify;
    // split on whether integrated, or whether asked for master
    if (t->usesCentralEqualityEngine() || esi.d_useMaster)
    {
      // the theory uses the central equality engine
      eet.d_usedEe = &d_centralEqualityEngine;
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
      TheoryState* ts = t->getTheoryState();
      if (ts != nullptr)
      {
        d_centralStates.push_back(ts);
      }
      continue;
    }
    eet.d_allocEe.reset(allocateEqualityEngine(esi, c));
    // the theory uses the equality engine
    eet.d_usedEe = eet.d_allocEe.get();
  }

  const LogicInfo& logicInfo = d_te.getLogicInfo();
  if (logicInfo.isQuantified())
  {
    // construct the master equality engine
    Assert(d_masterEqualityEngine == nullptr);
    QuantifiersEngine* qe = d_te.getQuantifiersEngine();
    Assert(qe != nullptr);
    d_masterEENotify.reset(new MasterNotifyClass(qe));
    d_masterEqualityEngine.reset(new eq::EqualityEngine(*d_masterEENotify.get(),
                                                        d_te.getSatContext(),
                                                        "theory::master",
                                                        false));

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
      if (t->usesCentralEqualityEngine())
      {
        continue;
      }
      EeTheoryInfo& eet = d_einfo[theoryId];
      // Get the allocated equality engine, and connect it to the master
      // equality engine.
      eq::EqualityEngine* eeAlloc = eet.d_allocEe.get();
      if (eeAlloc != nullptr)
      {
        // set the master equality engine of the theory's equality engine
        eeAlloc->setMasterEqualityEngine(d_masterEqualityEngine.get());
      }
    }
  }
  // ----- test
  // set the master equality engine of the theory's equality engine
  d_centralEqualityEngine.setMasterEqualityEngine(d_masterEqualityEngine.get());
  // ----- end test
}

void EqEngineManagerTest::MasterNotifyClass::eqNotifyNewClass(TNode t)
{
  // adds t to the quantifiers term database
  d_quantEngine->eqNotifyNewClass(t);
}

//================================================ central

void EqEngineManagerTest::notifyBuildingModel() {}

EqEngineManagerTest::CentralNotifyClass::CentralNotifyClass(
    EqEngineManagerTest& eemc)
    : d_eemc(eemc), d_mNotify(nullptr), d_quantEngine(nullptr)
{
}

bool EqEngineManagerTest::CentralNotifyClass::eqNotifyTriggerPredicate(
    TNode predicate, bool value)
{
  Trace("eem-test") << "eqNotifyTriggerPredicate: " << predicate << std::endl;
  return d_eemc.eqNotifyTriggerPredicate(predicate, value);
}

bool EqEngineManagerTest::CentralNotifyClass::eqNotifyTriggerTermEquality(
    TheoryId tag, TNode t1, TNode t2, bool value)
{
  Trace("eem-test") << "eqNotifyTriggerTermEquality: " << t1 << " " << t2
                    << value << ", tag = " << tag << std::endl;
  return d_eemc.eqNotifyTriggerTermEquality(tag, t1, t2, value);
}

void EqEngineManagerTest::CentralNotifyClass::eqNotifyConstantTermMerge(
    TNode t1, TNode t2)
{
  Trace("eem-test") << "eqNotifyConstantTermMerge: " << t1 << " " << t2
                    << std::endl;
  d_eemc.eqNotifyConstantTermMerge(t1, t2);
}

void EqEngineManagerTest::CentralNotifyClass::eqNotifyNewClass(TNode t)
{
  Trace("eem-test") << "...eqNotifyNewClass " << t << std::endl;
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

void EqEngineManagerTest::CentralNotifyClass::eqNotifyMerge(TNode t1, TNode t2)
{
  Trace("eem-test") << "...eqNotifyMerge " << t1 << ", " << t2 << std::endl;
  // notify all theories that have merge notifications
  for (eq::EqualityEngineNotify* notify : d_mergeNotify)
  {
    notify->eqNotifyMerge(t1, t2);
  }
}

void EqEngineManagerTest::CentralNotifyClass::eqNotifyDisequal(TNode t1,
                                                               TNode t2,
                                                               TNode reason)
{
  Trace("eem-test") << "...eqNotifyDisequal " << t1 << ", " << t2 << std::endl;
  // notify all theories that have disequal notifications
  for (eq::EqualityEngineNotify* notify : d_disequalNotify)
  {
    notify->eqNotifyDisequal(t1, t2, reason);
  }
}

bool EqEngineManagerTest::eqNotifyTriggerPredicate(TNode predicate, bool value)
{
  // if we're building model, ignore this propagation
  if (d_buildingModel.get())
  {
    return true;
  }
  // always propagate with the shared solver
  Trace("eem-test") << "...propagate " << predicate << ", " << value
                    << " with shared solver" << std::endl;
  bool ok = d_sharedSolver.propagateLit(predicate, value);
  if (!ok)
  {
    notifyInConflict();
  }
  return ok;
}

bool EqEngineManagerTest::eqNotifyTriggerTermEquality(TheoryId tag,
                                                      TNode a,
                                                      TNode b,
                                                      bool value)
{
  // propagate to theory engine
  bool ok = d_sharedSolver.propagateLit(a.eqNode(b), value);
  if (!ok)
  {
    notifyInConflict();
    return false;
  }
  // propagate shared equality
  return d_sharedSolver.propagateSharedEquality(tag, a, b, value);
}

void EqEngineManagerTest::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  Node lit = t1.eqNode(t2);
  Node conflict = d_centralEqualityEngine.mkExplainLit(lit);
  Trace("eem-test") << "...explained conflict of " << lit << " ... " << conflict
                    << std::endl;
  notifyInConflict();
  d_sharedSolver.sendConflict(TrustNode::mkTrustConflict(conflict));
  return;
}

void EqEngineManagerTest::notifyInConflict()
{
  // notify the states we are in conflict
  for (TheoryState* cs : d_centralStates)
  {
    cs->notifyInConflict();
  }
}

}  // namespace theory
}  // namespace CVC4
