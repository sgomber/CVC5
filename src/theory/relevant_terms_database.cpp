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

namespace CVC4 {
namespace theory {

RelevantTermsDatabase::RelevantTermsDatabase() {}

bool RelevantTermsDatabase::isRelevant(TNode t) const
{
  return d_relevantTerms.find(t) != d_relevantTerms.end();
}

void RelevantTermsDatabase::addRelevantTerms(const std::set<Node>& termSet)
{
  d_relevantTerms.insert(termSet.begin(), termSet.end());
}

void RelevantTermsDatabase::addRelevantTerm(TNode t)
{
  Assert (d_irrKinds.find(t.getKind()) == d_irrKinds.end());
  Trace("rel-term-db") << "RelevantTermsDatabase: adding " << t << std::endl;
  d_relevantTerms.insert(t);
}

const std::set<Node>& RelevantTermsDatabase::getRelevantTerms() const
{
  return d_relevantTerms;
}

void RelevantTermsDatabase::setIrrelevantKind(Kind k) { d_irrKinds.insert(k); }

const std::set<Kind>& RelevantTermsDatabase::getIrrelevantKinds() const
{
  return d_irrKinds;
}

void RelevantTermsDatabase::clear() { d_relevantTerms.clear(); }

}  // namespace theory
}  // namespace CVC4
