/*********************                                                        */
/*! \file combination_care_graph.cpp
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

#include "theory/combination_care_graph.h"

#include "expr/node_visitor.h"
#include "theory/care_graph.h"
#include "theory/ee_manager_central.h"
#include "theory/ee_manager_distributed.h"
#include "theory/model_manager_central.h"
#include "theory/model_manager_distributed.h"
#include "theory/shared_solver_distributed.h"
#include "theory/shared_terms_database.h"
#include "theory/term_registration_visitor.h"
#include "theory/theory_engine.h"
//#include "theory/shared_solver_central.h"

namespace CVC4 {
namespace theory {

CombinationEngine::CombinationEngine(TheoryEngine& te,
                                     const std::vector<Theory*>& paraTheories)
    : d_te(te),
      d_logicInfo(te.getLogicInfo()),
      d_paraTheories(paraTheories),
      d_paraSet(0),
      d_eemUse(nullptr),
      d_mmUse(nullptr) d_ssUse(nullptr)
{
}

CombinationEngine::~CombinationEngine() {}

void CombinationEngine::finishInit()
{
  // create the equality engine, model manager, and shared solver
  if (options::eeMode() == options::EqEngineMode::DISTRIBUTED)
  {
    // make the distributed equality engine manager
    std::unique_ptr<EqEngineManagerDistributed> eeDistributed(
        new EqEngineManagerDistributed(d_te));
    // make the distributed model manager
    d_mmUse.reset(new ModelManagerDistributed(d_te, *eeDistributed.get()));
    d_eemUse = std::move(eeDistributed);
    // use the distributed shared solver
    d_ssUse.reset(new SharedSolverDistributed(d_te));
  }
  else if (options::eeMode() == options::EqEngineMode::CENTRAL)
  {
    d_eemUse.reset(new EqEngineManagerCentral(d_te));
    d_mmUse.reset(new ModelManagerCentral(d_te));
    // d_ssUse.reset(new SharedSolverCentral(d_te));
  }
  else
  {
    Unhandled() << "CombinationEngine::finishInit: equality engine mode "
                << options::eeMode() << " not supported";
  }

  Assert(d_eemUse != nullptr);
  // initialize equality engines in all theories, including quantifiers engine
  d_eemUse->initializeTheories(d_ssUse.get());

  Assert(d_mmUse != nullptr);
  // initialize the model manager
  d_mmUse->finishInit();

  // initialize equality engine of the model using the equality engine manager
  TheoryModel* m = d_mmUse->getModel();
  d_eemUse->initializeModel(m);
}

const EeTheoryInfo* CombinationEngine::getEeTheoryInfo(TheoryId tid) const
{
  return d_eemUse->getEeTheoryInfo(tid);
}

eq::EqualityEngine* CombinationEngine::getCoreEqualityEngine()
{
  return d_eemUse->getCoreEqualityEngine();
}

void CombinationEngine::resetModel() { d_mmUse->resetModel(); }

void CombinationEngine::postProcessModel(bool incomplete)
{
  // should have a consistent core equality engine
  eq::EqualityEngine* mee = d_eemUse->getCoreEqualityEngine();
  if (mee != nullptr)
  {
    AlwaysAssert(mee->consistent());
  }
  // postprocess with the model
  d_mmUse->postProcessModel(incomplete);
}

theory::TheoryModel* CombinationEngine::getModel()
{
  return d_mmUse->getModel();
}

SharedSolver* CombinationEngine::getSharedSolver() { return d_ssUse.get(); }

void CombinationEngine::sendLemma(TNode node, TheoryId atomsTo)
{
  d_te.lemma(node, RULE_INVALID, false, LemmaProperty::NONE, atomsTo);
}

bool CombinationEngine::isParametric(TheoryId tid) const
{
  // FIXME
  return true;
}

}  // namespace theory
}  // namespace CVC4
