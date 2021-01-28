/*********************                                                        */
/*! \file lazy_tpp_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The lazy theory preprocess solver
 **/
#include "prop/lazy_tpp_solver.h"

#include "prop/prop_engine.h"

namespace CVC4 {
namespace prop {

LazyTppSolver::LazyTppSolver(PropEngine& propEngine,
                             TheoryEngine& theoryEngine,
                             context::UserContext* userContext,
                             ProofNodeManager* pnm)
    : TheoryPreprocessSolver(propEngine, theoryEngine, userContext, pnm),
      d_processedSkolems(userContext),
      d_lemmasAdded(false)
{
}

LazyTppSolver::~LazyTppSolver() {}

void LazyTppSolver::notifyAssertFact(TNode assertion)
{
  Trace("lazy-tpp") << "LazyTppSolver::notifyAssertFact: " << assertion
                    << std::endl;
  // determine which skolems become activated, these will be processed
  // immediately after this call in check(...).
  d_rtf.getSkolems(assertion, d_activeSkolems);
}

theory::TrustNode LazyTppSolver::preprocessLemma(
    theory::TrustNode trn,
    std::vector<theory::TrustNode>& newLemmas,
    std::vector<Node>& newSkolems,
    Node& retLemma)
{
  // version without fixed point or lemmas
  std::vector<theory::TrustNode> ppLemmas;
  std::vector<Node> ppSkolems;
  theory::TrustNode ret =
      d_tpp.preprocessLemma(trn, ppLemmas, ppSkolems, true, false);
  retLemma = makeReturnLemma(ret, ppLemmas);
  return ret;
}

theory::TrustNode LazyTppSolver::preprocess(
    TNode node,
    std::vector<theory::TrustNode>& newLemmas,
    std::vector<Node>& newSkolems)
{
  // version without fixed point or lemmas
  return d_tpp.preprocess(node, true);
}

theory::TrustNode LazyTppSolver::removeItes(
    TNode node,
    std::vector<theory::TrustNode>& ppLemmas,
    std::vector<Node>& ppSkolems)
{
  // run the remove term formula utility directly, version without lemma
  // tracking or fixed point
  return d_rtf.run(node);
}

void LazyTppSolver::check(theory::Theory::Effort effort)
{
  Trace("lazy-tpp") << "LazyTppSolver::check: " << effort << std::endl;
  d_lemmasAdded = false;
  // add lemmas for each skolem
  for (const Node& k : d_activeSkolems)
  {
    if (d_processedSkolems.find(k) != d_processedSkolems.end())
    {
      Trace("lazy-tpp") << "- already process skolem " << k << std::endl;
      continue;
    }
    Trace("lazy-tpp") << "- process skolem " << k << std::endl;
    theory::TrustNode lem = d_rtf.getLemmaForSkolem(k);
    Trace("lazy-tpp") << "...lemma is " << lem.getNode() << std::endl;

    // add lemma to prop engine
    // TODO: technically losing skolem connection here
    d_propEngine.assertLemma(lem);
    d_lemmasAdded = true;

    d_processedSkolems.insert(k);
  }
  d_activeSkolems.clear();
}

bool LazyTppSolver::needCheck() { return d_lemmasAdded; }

}  // namespace prop
}  // namespace CVC4
