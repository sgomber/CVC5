/*********************                                                        */
/*! \file combination_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a care graph based approach for theory combination.
 **/

#include "theory/combination_engine.h"

#include "expr/node_visitor.h"
#include "theory/care_graph.h"
#include "theory/ee_manager_central.h"
#include "theory/ee_manager_distributed.h"
#include "theory/ee_manager_test.h"
#include "theory/model_manager_central.h"
#include "theory/model_manager_distributed.h"
#include "theory/shared_solver_central.h"
#include "theory/shared_solver_distributed.h"
#include "theory/shared_solver_test.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

CombinationEngine::CombinationEngine(TheoryEngine& te,
                                     const std::vector<Theory*>& paraTheories,
                                     ProofNodeManager* pnm)
    : d_te(te),
      d_logicInfo(te.getLogicInfo()),
      d_paraTheories(paraTheories),
      d_paraSet(0),
      d_eemanager(nullptr),
      d_mmanager(nullptr),
      d_sharedSolver(nullptr),
      d_cmbsPg(pnm ? new EagerProofGenerator(pnm, te.getUserContext())
                   : nullptr)
{
}

CombinationEngine::~CombinationEngine() {}

void CombinationEngine::finishInit()
{
  // create the equality engine, model manager, and shared solver
  if (options::eeMode() == options::EqEngineMode::DISTRIBUTED)
  {
    // use the distributed shared solver
    d_sharedSolver.reset(new SharedSolverDistributed(d_te));
    // make the distributed equality engine manager
    d_eemanager.reset(
        new EqEngineManagerDistributed(d_te, *d_sharedSolver.get()));
    // make the distributed model manager
    d_mmanager.reset(new ModelManagerDistributed(d_te, *d_eemanager.get()));
  }
  else if (options::eeMode() == options::EqEngineMode::TEST)
  {
    // use the distributed shared solver
    d_sharedSolver.reset(new SharedSolverTest(d_te));
    // make the distributed equality engine manager
    d_eemanager.reset(new EqEngineManagerTest(d_te, *d_sharedSolver.get()));
    // make the distributed model manager
    d_mmanager.reset(new ModelManagerDistributed(d_te, *d_eemanager.get()));
  }
  else if (options::eeMode() == options::EqEngineMode::CENTRAL)
  {
    // use the central shared solver
    d_sharedSolver.reset(new SharedSolverCentral(d_te));
    // make the central equality engine manager
    d_eemanager.reset(new EqEngineManagerCentral(d_te, *d_sharedSolver.get()));
    // d_mmanager.reset(new ModelManagerCentral(d_te, *eeCentral.get()));
    d_mmanager.reset(new ModelManagerDistributed(d_te, *d_eemanager.get()));
  }
  else
  {
    Unhandled() << "CombinationEngine::finishInit: equality engine mode "
                << options::eeMode() << " not supported";
  }

  Assert(d_eemanager != nullptr);

  // initialize equality engines in all theories, including quantifiers engine
  // and the (provided) shared solver
  d_eemanager->initializeTheories();

  Assert(d_mmanager != nullptr);
  // initialize the model manager, based on the notify object of this class
  eq::EqualityEngineNotify* meen = getModelEqualityEngineNotify();
  d_mmanager->finishInit(meen);
}

const EeTheoryInfo* CombinationEngine::getEeTheoryInfo(TheoryId tid) const
{
  return d_eemanager->getEeTheoryInfo(tid);
}

eq::EqualityEngine* CombinationEngine::getCoreEqualityEngine()
{
  return d_eemanager->getCoreEqualityEngine();
}

void CombinationEngine::resetModel() { d_mmanager->resetModel(); }

void CombinationEngine::postProcessModel(bool incomplete)
{
  // should have a consistent core equality engine
  eq::EqualityEngine* mee = d_eemanager->getCoreEqualityEngine();
  if (mee != nullptr)
  {
    AlwaysAssert(mee->consistent());
  }
  // postprocess with the model
  d_mmanager->postProcessModel(incomplete);
}

theory::TheoryModel* CombinationEngine::getModel()
{
  return d_mmanager->getModel();
}

SharedSolver* CombinationEngine::getSharedSolver()
{
  return d_sharedSolver.get();
}
bool CombinationEngine::isProofEnabled() const { return d_cmbsPg != nullptr; }

eq::EqualityEngineNotify* CombinationEngine::getModelEqualityEngineNotify()
{
  return nullptr;
}

void CombinationEngine::sendLemma(TrustNode trn, TheoryId atomsTo)
{
  d_te.lemma(trn, LemmaProperty::NONE, atomsTo);
}

bool CombinationEngine::isParametric(TheoryId tid) const
{
  // FIXME: necessary?
  return true;
}

void CombinationEngine::resetRound()
{
  // compute the relevant terms?
}

const std::unordered_set<Node, NodeHashFunction>&
CombinationEngine::getEqcRepresentatives() const
{
  return d_eemanager->getEqcRepresentatives();
}

const std::vector<Node>& CombinationEngine::getEqcRepresentativesForType(
    TypeNode t) const
{
  return d_eemanager->getEqcRepresentativesForType(t);
}

}  // namespace theory
}  // namespace CVC4
