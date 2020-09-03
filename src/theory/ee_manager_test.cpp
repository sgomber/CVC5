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

namespace CVC4 {
namespace theory {

EqEngineManagerTest::EqEngineManagerTest(TheoryEngine& te, SharedSolver& shs)
    : EqEngineManager(te, shs), d_masterEENotify(nullptr),
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
    // allocate an equality engine for the shared terms database
    d_stbEqualityEngine.reset(allocateEqualityEngine(esis, c));
    d_sharedSolver.setEqualityEngine(d_stbEqualityEngine.get());
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
}

void EqEngineManagerTest::MasterNotifyClass::eqNotifyNewClass(TNode t)
{
  // adds t to the quantifiers term database
  d_quantEngine->eqNotifyNewClass(t);
}

eq::EqualityEngine* EqEngineManagerTest::getCoreEqualityEngine()
{
  return d_masterEqualityEngine.get();
}

//================================================ central


void EqEngineManagerTest::notifyBuildingModel()
{
}
  
EqEngineManagerTest::CentralNotifyClass::CentralNotifyClass(
    EqEngineManagerTest& eemc)
    : d_eemc(eemc), d_mNotify(nullptr), d_quantEngine(nullptr)
{
}

bool EqEngineManagerTest::CentralNotifyClass::eqNotifyTriggerPredicate(
    TNode predicate, bool value)
{
  Trace("eem-test") << "eqNotifyTriggerPredicate: " << predicate
                       << std::endl;
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

void EqEngineManagerTest::CentralNotifyClass::eqNotifyMerge(TNode t1,
                                                               TNode t2)
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
  Trace("eem-test") << "...eqNotifyDisequal " << t1 << ", " << t2
                       << std::endl;
  // notify all theories that have disequal notifications
  for (eq::EqualityEngineNotify* notify : d_disequalNotify)
  {
    notify->eqNotifyDisequal(t1, t2, reason);
  }
}

bool EqEngineManagerTest::eqNotifyTriggerPredicate(TNode predicate,
                                                      bool value)
{
  // if we're building model, ignore this propagation
  if (d_buildingModel.get())
  {
    return true;
  }
  // always propagate with the shared solver
  Trace("eem-test") << "...propagate " << predicate << ", " << value
                       << " with shared solver" << std::endl;
  return d_sharedSolver.propagateLit(predicate, value);
}

bool EqEngineManagerTest::eqNotifyTriggerTermEquality(TheoryId tag,
                                                         TNode a,
                                                         TNode b,
                                                         bool value)
{
  return d_sharedSolver.propagateSharedEquality(tag, a, b, value);
}

void EqEngineManagerTest::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  Node lit = t1.eqNode(t2);
  Node conflict = d_centralEqualityEngine.mkExplainLit(lit);
  Trace("eem-test") << "...explained conflict of " << lit << " ... "
                        << conflict << std::endl;
  d_sharedSolver.sendConflict(TrustNode::mkTrustConflict(conflict));
  return;
}

}  // namespace theory
}  // namespace CVC4
