/*********************                                                        */
/*! \file shared_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The shared solver base class
 **/

#include "theory/shared_solver.h"

#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

// Always creates shared terms database. In all cases, shared terms
// database is used as a way of tracking which calls to Theory::addSharedTerm
// we need to make in preNotifySharedFact.
// In distributed equality engine management, shared terms database also
// maintains an equality engine. In central equality engine management,
// it does not.
SharedSolver::SharedSolver(TheoryEngine& te,
                           const std::vector<Theory*>& paraTheories)
    : d_te(te),
      d_logicInfo(te.getLogicInfo()),
      d_paraTheories(paraTheories),
      d_sharedTerms(&d_te, d_te.getSatContext()),
      d_sharedTermsVisitor(d_sharedTerms)
{
}

SharedSolver::~SharedSolver() {}

void SharedSolver::preRegisterShared(TNode t, bool multipleTheories)
{
  // register it with the equality engine manager if shared is enabled
  if (d_logicInfo.isSharingEnabled())
  {
    preRegisterSharedInternal(t);
  }
  // if multiple theories are present in t
  if (multipleTheories)
  {
    // Collect the shared terms if there are multiple theories
    // This calls d_sharedTerms->addSharedTerm, possible multiple times
    NodeVisitor<SharedTermsVisitor>::run(*d_sharedTermsVisitor.get(), t);
  }
}

void SharedSolver::preNotifySharedFact(TNode atom)
{
  Assert(d_sharedTerms != nullptr);
  if (d_sharedTerms->hasSharedTerms(atom))
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
          // call the add shared term method
          t->addSharedTerm(term);
        }
      }
      d_sharedTerms->markNotified(term, theories);
    }
  }
}

EqualityStatus SharedSolver::getEqualityStatus(TNode a, TNode b)
{
  Assert(a.getType().isComparableTo(b.getType()));
  // does it have an equality status based on the equality engine manager?
  EqualityStatus estatus = getEqualityStatusInternal(a, b);
  if (estatus != EQUALITY_UNKNOWN)
  {
    return estatus;
  }
  return d_te.theoryOf(Theory::theoryOf(a.getType()))->getEqualityStatus(a, b);
}

TrustNode SharedSolver::explain(TNode literal, TheoryId theory) const
{
  TrustNode texp;
  if (theory == THEORY_BUILTIN)
  {
    // explanation based on equality engine manager
    texp = explainSharedInternal(literal);
    Debug("theory::explain")
        << "\tTerm was propagated by THEORY_BUILTIN. Explanation: "
        << texp.getNode() << std::endl;
  }
  else
  {
    texp = d_te.theoryOf(theory)->explain(literal);
    Debug("theory::explain")
        << "\tTerm was propagated by owner theory: " << theory
        << ". Explanation: " << texp.getNode() << std::endl;
  }
  return texp;
}

void SharedSolver::assertSharedEquality(TNode equality,
                                        bool polarity,
                                        TNode reason)
{
  // do nothing
}

}  // namespace theory
}  // namespace CVC4
