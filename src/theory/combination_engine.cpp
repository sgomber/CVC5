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
#include "theory/shared_terms_database.h"
#include "theory/term_registration_visitor.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

CombinationEngine::CombinationEngine(TheoryEngine& te,
                                     const std::vector<Theory*>& paraTheories)
    : d_te(te),
      d_logicInfo(te.getLogicInfo()),
      d_paraTheories(paraTheories),
      d_eemUse(nullptr),
      d_mmUse(nullptr),
      d_sharedTerms(nullptr),
      d_sharedTermsVisitor(nullptr)
{
}

CombinationEngine::~CombinationEngine() {}

void CombinationEngine::finishInit()
{
  // create the equality engine and model managers
  if (options::eeMode() == options::EqEngineMode::DISTRIBUTED)
  {
    // distributed equality engine always needs shared terms database
    d_sharedTerms.reset(new SharedTermsDatabase(&d_te, d_te.getSatContext()));
    d_sharedTermsVisitor.reset(new SharedTermsVisitor(*d_sharedTerms.get()));
    // make the distributed equality engine manager
    std::unique_ptr<EqEngineManagerDistributed> eeDistributed(
        new EqEngineManagerDistributed(d_te, d_sharedTerms.get()));
    // make the distributed model manager
    d_mmUse.reset(new ModelManagerDistributed(d_te, *eeDistributed.get()));
    d_eemUse = std::move(eeDistributed);
  }
  else if (options::eeMode() == options::EqEngineMode::CENTRAL)
  {
    d_eemUse.reset(new EqEngineManagerCentral(d_te, nullptr));
    d_mmUse.reset(new ModelManagerCentral(d_te));
  }
  else
  {
    Unhandled() << "CombinationEngine::finishInit: equality engine mode "
                << options::eeMode() << " not supported";
  }

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

void CombinationEngine::preRegister(TNode t, bool multipleTheories)
{
  if (d_sharedTerms == nullptr)
  {
    return;
  }
  if (d_logicInfo.isSharingEnabled() && t.getKind() == kind::EQUAL)
  {
    // When sharing is enabled, we propagate from the shared terms manager also
    d_sharedTerms->addEqualityToPropagate(t);
  }
  if (multipleTheories)
  {
    // Collect the shared terms if there are multiple theories
    NodeVisitor<SharedTermsVisitor>::run(*d_sharedTermsVisitor.get(), t);
  }
}

void CombinationEngine::notifyAssertFact(TNode atom)
{
  if (d_sharedTerms != nullptr && d_sharedTerms->hasSharedTerms(atom))
  {
    // Notify the theories the shared terms
    SharedTermsDatabase::shared_terms_iterator it = d_sharedTerms->begin(atom);
    SharedTermsDatabase::shared_terms_iterator it_end =
        d_sharedTerms->end(atom);
    for (; it != it_end; ++it)
    {
      TNode term = *it;
      Theory::Set theories = d_sharedTerms->getTheoriesToNotify(atom, term);
      for (TheoryId id = THEORY_FIRST; id != THEORY_LAST; ++id)
      {
        if (Theory::setContains(id, theories))
        {
          Theory* t = d_te.theoryOf(id);
          // call the notify shared term method
          t->notifySharedTerm(term);
        }
      }
      d_sharedTerms->markNotified(term, theories);
    }
  }
}

bool CombinationEngine::isShared(TNode term) const
{
  if (d_sharedTerms != nullptr)
  {
    return d_sharedTerms->isShared(term);
  }
  // otherwise, always assume its shared
  return true;
}

EqualityStatus CombinationEngine::getEqualityStatus(TNode a, TNode b)
{
  Assert(a.getType().isComparableTo(b.getType()));
  if (d_sharedTerms != nullptr)
  {
    // if we're using a shared terms database, ask its status if a and b are
    // shared.
    if (d_sharedTerms->isShared(a) && d_sharedTerms->isShared(b))
    {
      if (d_sharedTerms->areEqual(a, b))
      {
        return EQUALITY_TRUE_AND_PROPAGATED;
      }
      else if (d_sharedTerms->areDisequal(a, b))
      {
        return EQUALITY_FALSE_AND_PROPAGATED;
      }
    }
  }
  return d_te.theoryOf(Theory::theoryOf(a.getType()))->getEqualityStatus(a, b);
}

Node CombinationEngine::explain(TNode literal) const
{
  if (d_sharedTerms == nullptr)
  {
    Unhandled() << "CombinationEngine::CombinationEngine: does not support the "
                   "explain interface";
  }
  return d_sharedTerms->explain(literal);
}

void CombinationEngine::assertEquality(TNode equality,
                                       bool polarity,
                                       TNode reason)
{
  if (d_sharedTerms != nullptr)
  {
    d_sharedTerms->assertEquality(equality, polarity, reason);
  }
}

bool CombinationEngine::needsPropagation(TNode literal, TheoryId theory)
{
  // by default, we always need propagation
  return true;
}

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
