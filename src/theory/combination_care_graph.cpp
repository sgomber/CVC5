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

CombinationCareGraph::CombinationCareGraph(
    TheoryEngine& te,
    const std::vector<Theory*>& paraTheories,
    context::Context* c)
    : d_te(te),
      d_logicInfo(te.getLogicInfo()),
      d_paraTheories(paraTheories),
      d_sharedTerms(&te, c),
      d_preRegistrationVisitor(&te, c),
      d_sharedTermsVisitor(d_sharedTerms),
      d_eemUse(nullptr),
      d_eeDistributed(nullptr),
      d_mmUse(nullptr),
      d_mDistributed(nullptr)
{
  if (options::eeMode() == options::EqEngineMode::DISTRIBUTED)
  {
    d_eeDistributed.reset(new EqEngineManagerDistributed(te, &d_sharedTerms));
    d_eemUse = d_eeDistributed.get();
    d_mDistributed.reset(new ModelManagerDistributed(te, *d_eeDistributed.get()));
    d_mmUse = d_mDistributed.get();
  }
  else
  {
    AlwaysAssert(false) << "CombinationCareGraph::CombinationCareGraph: equality engine mode "
                        << options::eeMode() << " not supported";
  }

  
}

CombinationCareGraph::~CombinationCareGraph() {}

void CombinationCareGraph::finishInit()
{
  Assert (d_eemUse!=nullptr);
  // initialize equality engines in all theories, including quantifiers engine
  d_eemUse->initializeTheories();
  
  Assert (d_mmUse!=nullptr);
  // initialize the model manager
  d_mmUse->finishInit();

  // initialize equality engine of the model using the equality engine manager
  TheoryModel * m = d_mmUse->getModel();
  d_eemUse->initializeModel(m);
}

void CombinationCareGraph::combineTheories()
{
  Trace("combineTheories") << "TheoryEngine::combineTheories()" << std::endl;

  // Care graph we'll be building
  CareGraph careGraph;

  // get the care graph from the parametric theories
  for (Theory* t : d_paraTheories)
  {
    t->getCareGraph(&careGraph);
  }

  Trace("combineTheories")
      << "TheoryEngine::combineTheories(): care graph size = "
      << careGraph.size() << std::endl;

  // Now add splitters for the ones we are interested in
  CareGraph::const_iterator care_it = careGraph.begin();
  CareGraph::const_iterator care_it_end = careGraph.end();

  prop::PropEngine* propEngine = d_te.getPropEngine();
  for (; care_it != care_it_end; ++care_it)
  {
    const CarePair& carePair = *care_it;

    Debug("combineTheories")
        << "TheoryEngine::combineTheories(): checking " << carePair.d_a << " = "
        << carePair.d_b << " from " << carePair.d_theory << std::endl;

    Assert(d_sharedTerms.isShared(carePair.d_a) || carePair.d_a.isConst());
    Assert(d_sharedTerms.isShared(carePair.d_b) || carePair.d_b.isConst());

    // The equality in question (order for no repetition)
    Node equality = carePair.d_a.eqNode(carePair.d_b);

    // We need to split on it
    Debug("combineTheories")
        << "TheoryEngine::combineTheories(): requesting a split " << std::endl;

    d_te.lemma(equality.orNode(equality.notNode()),
               RULE_INVALID,
               false,
               LemmaProperty::NONE,
               carePair.d_theory);

    // Could check the equality status here:
    //   EqualityStatus es = getEqualityStatus(carePair.d_a, carePair.d_b);
    // and only require true phase below if:
    //   es == EQUALITY_TRUE || es == EQUALITY_TRUE_IN_MODEL
    // and require false phase below if:
    //   es == EQUALITY_FALSE_IN_MODEL
    // This is supposed to force preference to follow what the theory models
    // already have but it doesn't seem to make a big difference - need to
    // explore more -Clark
    Node e = d_te.ensureLiteral(equality);
    propEngine->requirePhase(e, true);
  }
}

const EeTheoryInfo* CombinationCareGraph::getEeTheoryInfo(TheoryId tid) const
{
  return d_eemUse->getEeTheoryInfo(tid);
}

eq::EqualityEngine* CombinationCareGraph::getCoreEqualityEngine()
{
  return d_eemUse->getCoreEqualityEngine();
}

void CombinationCareGraph::resetModel() { d_mmUse->resetModel(); }

bool CombinationCareGraph::buildModel() { return d_mmUse->buildModel(); }

void CombinationCareGraph::postProcessModel(bool incomplete)
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

theory::TheoryModel* CombinationCareGraph::getModel()
{
  return d_mmUse->getModel();
}

void CombinationCareGraph::preRegister(TNode t)
{
  if (d_logicInfo.isSharingEnabled() && t.getKind() == kind::EQUAL)
  {
    // When sharing is enabled, we propagate from the shared terms manager also
    d_sharedTerms.addEqualityToPropagate(t);
  }
  // Pre-register the terms in the atom
  Theory::Set theories =
      NodeVisitor<PreRegisterVisitor>::run(d_preRegistrationVisitor, t);
  theories = Theory::setRemove(THEORY_BOOL, theories);
  // Remove the top theory, if any more that means multiple theories were
  // involved
  bool multipleTheories = Theory::setRemove(Theory::theoryOf(t), theories);
  TheoryId i;
  // These checks don't work with finite model finding, because it
  // uses Rational constants to represent cardinality constraints,
  // even though arithmetic isn't actually involved.
  if (!options::finiteModelFind())
  {
    while ((i = Theory::setPop(theories)) != THEORY_LAST)
    {
      if (!d_logicInfo.isTheoryEnabled(i))
      {
        LogicInfo newLogicInfo = d_logicInfo.getUnlockedCopy();
        newLogicInfo.enableTheory(i);
        newLogicInfo.lock();
        std::stringstream ss;
        ss << "The logic was specified as " << d_logicInfo.getLogicString()
           << ", which doesn't include " << i
           << ", but found a term in that theory." << std::endl
           << "You might want to extend your logic to "
           << newLogicInfo.getLogicString() << std::endl;
        throw LogicException(ss.str());
      }
    }
  }
  if (multipleTheories)
  {
    // Collect the shared terms if there are multiple theories
    NodeVisitor<SharedTermsVisitor>::run(d_sharedTermsVisitor, t);
  }
}
void CombinationCareGraph::notifyAssertFact(TNode atom)
{
  if (d_sharedTerms.hasSharedTerms(atom))
  {
    // Notify the theories the shared terms
    SharedTermsDatabase::shared_terms_iterator it = d_sharedTerms.begin(atom);
    SharedTermsDatabase::shared_terms_iterator it_end = d_sharedTerms.end(atom);
    for (; it != it_end; ++it)
    {
      TNode term = *it;
      Theory::Set theories = d_sharedTerms.getTheoriesToNotify(atom, term);
      for (TheoryId id = THEORY_FIRST; id != THEORY_LAST; ++id)
      {
        if (Theory::setContains(id, theories))
        {
          // call the add shared term internal method of theory engine
          d_te.addSharedTermInternal(id, term);
        }
      }
      d_sharedTerms.markNotified(term, theories);
    }
  }
}

bool CombinationCareGraph::isShared(TNode term) const
{
  return d_sharedTerms.isShared(term);
}

theory::EqualityStatus CombinationCareGraph::getEqualityStatus(TNode a, TNode b)
{
  Assert(a.getType().isComparableTo(b.getType()));
  if (d_sharedTerms.isShared(a) && d_sharedTerms.isShared(b))
  {
    if (d_sharedTerms.areEqual(a, b))
    {
      return EQUALITY_TRUE_AND_PROPAGATED;
    }
    else if (d_sharedTerms.areDisequal(a, b))
    {
      return EQUALITY_FALSE_AND_PROPAGATED;
    }
  }
  return d_te.theoryOf(Theory::theoryOf(a.getType()))->getEqualityStatus(a, b);
}

Node CombinationCareGraph::explain(TNode literal) const
{
  return d_sharedTerms.explain(literal);
}

void CombinationCareGraph::assertEquality(TNode equality,
                                          bool polarity,
                                          TNode reason)
{
  d_sharedTerms.assertEquality(equality, polarity, reason);
}

bool CombinationCareGraph::needsPropagation(TNode literal, theory::TheoryId theory)
{
  return true;
}
  
}  // namespace theory
}  // namespace CVC4
