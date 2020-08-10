/*********************                                                        */
/*! \file combination_distributed.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for theory combination.
 **/

#include "theory/combination_distributed.h"

#include "theory/care_graph.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

CombinationDistributed::CombinationDistributed(
    TheoryEngine& te,
    const std::vector<Theory*>& paraTheories,
    context::Context* c)
    : d_te(te),
      d_paraTheories(paraTheories),
      d_sharedTerms(&te, c),
      d_eeDistributed(new EqEngineManagerDistributed(te)),
      d_mDistributed(new ModelManagerDistributed(te, *d_eeDistributed.get()))
{
}

CombinationDistributed::~CombinationDistributed() {}

void CombinationDistributed::finishInit()
{
  // initialize equality engines in all theories
  d_eeDistributed->initializeTheories();
  // initialize the model
  d_mDistributed->finishInit();
}

void CombinationDistributed::combineTheories()
{
  Trace("combineTheories") << "TheoryEngine::combineTheories()" << std::endl;

  const LogicInfo& logicInfo = d_te.getLogicInfo();

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
    // and only require true phase belowif:
    //   es == EQUALITY_TRUE || es == EQUALITY_TRUE_IN_MODEL
    // and only require false phase below if:
    //   es == EQUALITY_FALSE_IN_MODEL
    // This is supposed to force preference to follow what the theory models
    // already have but it doesn't seem to make a big difference - need to
    // explore more -Clark
    Node e = d_te.ensureLiteral(equality);
    propEngine->requirePhase(e, true);
  }
}

void CombinationDistributed::resetModel() { d_mDistributed->resetModel(); }

bool CombinationDistributed::buildModel()
{
  return d_mDistributed->buildModel();
}

void CombinationDistributed::postProcessModel(bool incomplete)
{
  d_mDistributed->postProcessModel(incomplete);
}

theory::TheoryModel* CombinationDistributed::getModel()
{
  return d_mDistributed->getModel();
}

}  // namespace theory
}  // namespace CVC4
