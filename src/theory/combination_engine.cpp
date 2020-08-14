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
#include "theory/theory_engine.h"

// TODO: remove
#include "options/quantifiers_options.h"

namespace CVC4 {
namespace theory {

CombinationEngine::CombinationEngine(TheoryEngine& te,
                                     const std::vector<Theory*>& paraTheories,
                                     context::Context* c)
    : d_te(te),
      d_logicInfo(te.getLogicInfo()),
      d_paraTheories(paraTheories),
      d_eemUse(nullptr),
      d_mmUse(nullptr)
{
}

CombinationEngine::~CombinationEngine() {}

void CombinationEngine::finishInit()
{
  // create the equality engine and model managers
  initializeInternal();

  Assert(d_eemUse != nullptr);
  // initialize equality engines in all theories, including quantifiers engine
  d_eemUse->initializeTheories();

  Assert(d_mmUse != nullptr);
  // initialize the model manager
  d_mmUse->finishInit();

  // initialize equality engine of the model using the equality engine manager
  TheoryModel* m = d_mmUse->getModel();
  d_eemUse->initializeModel(m);
}

void CombinationEngine::initializeInternal()
{
  Unhandled() << "CombinationEngine::CombinationEngine: equality engine mode "
              << options::eeMode() << " not supported";
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

bool CombinationEngine::buildModel() { return d_mmUse->buildModel(); }

void CombinationEngine::postProcessModel(bool incomplete)
{
  // should have a consistent core equality engine
  eq::EqualityEngine* mee = d_eemUse->getCoreEqualityEngine();
  if (mee != NULL)
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

void CombinationEngine::preRegister(TNode preprocessed, bool multipleTheories)
{
}
void CombinationEngine::notifyAssertFact(TNode atom) {}
bool CombinationEngine::isShared(TNode term) const { return true; }

EqualityStatus CombinationEngine::getEqualityStatus(TNode a, TNode b)
{
  Assert(a.getType().isComparableTo(b.getType()));
  return d_te.theoryOf(Theory::theoryOf(a.getType()))->getEqualityStatus(a, b);
}

Node CombinationEngine::explain(TNode literal) const
{
  Unhandled() << "CombinationEngine::CombinationEngine: does not support the "
                 "explain interface";
  return Node::null();
}
void CombinationEngine::assertEquality(TNode equality,
                                       bool polarity,
                                       TNode reason)
{
}

bool CombinationEngine::needsPropagation(TNode literal, TheoryId theory)
{
  return true;
}

}  // namespace theory
}  // namespace CVC4
