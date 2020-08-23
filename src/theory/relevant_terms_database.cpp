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
    // get terms in the assertions of each theory
    for (context::CDList<Assertion>::const_iterator it = t->facts_begin(),
                                                    it_end = t->facts_end();
         it != itEnd;
         ++it)
    {
      collectTerms(*it, irrKinds);
    }
    // compute additional relevant terms
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

void RelevantTermsDatabase::collectTerms(TNode n,
                                         const std::set<Kind>& irrKinds)
{
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (d_relevantTerms.find(t) != d_relevantTerms.end())
    {
      // already visited
      continue;
    }
    Kind nk = n.getKind();
    if (irrKinds.find(nk) == irrKinds.end())
    {
      Trace("theory::collectTerms")
          << "Theory::collectTerms: adding " << n << endl;
      addRelevantTerm(n);
    }
    visit.insert(visit.end(), cur.begin(), cur.end());
  } while (!visit.empty());
}

void RelevantTermsDatabase::clear() { d_relevantTerms.clear(); }

}  // namespace theory
}  // namespace CVC4
