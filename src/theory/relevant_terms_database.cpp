/*********************                                                        */
/*! \file relevant_terms_database.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Relevant terms database
 **/

#include "theory/relevant_terms_database.h"

#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

RelevantTermsDatabase::RelevantTermsDatabase(TheoryEngine& te) : d_te(te) {}

void RelevantTermsDatabase::compute()
{
  const std::set<Kind>& irrKinds = d_te.getModel()->getIrrelevantKinds();
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
    // compute relevant terms in assertions
    t->computeAssertedTerms(*this, irrKinds);
    // compute relevant terms
    t->computeRelevantTerms(*this, irrKinds);
  }
}

bool RelevantTermsDatabase::isRelevant(TNode t) const
{
  return d_relevantTerms.find(t) != d_relevantTerms.end();
}

void RelevantTermsDatabase::addRelevantTerm(TNode t)
{
  d_relevantTerms.insert(t);
}

std::set<Node>& RelevantTermsDatabase::getRelevantTerms()
{
  return d_relevantTerms;
}

}  // namespace theory
}  // namespace CVC4
