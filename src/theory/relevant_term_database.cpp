/*********************                                                        */
/*! \file relevant_term_database.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base class for shared solver
 **/

#include "theory/relevant_term_database.h"

namespace CVC4 {
namespace theory {

RelevantTermDatabase::RelevantTermDatabase(TheoryEngine& te) : d_te(te) {}

void RelevantTermDatabase::compute()
{
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
    t->computeRelevantTermsInternal(d_relevantTerms);
    // compute relevant terms
    t->computeRelevantTerms(d_relevantTerms);
  }
}

bool RelevantTermDatabase::isRelevant(TNode t) const
{
  return d_relevantTerms.find(t) != d_relevantTerms.end();
}

void RelevantTermDatabase::addRelevantTerm(TNode t)
{
  d_relevantTerms.insert(t);
}

}  // namespace theory
}  // namespace CVC4
