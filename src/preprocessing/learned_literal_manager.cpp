/*********************                                                        */
/*! \file learned_literal_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   AAndrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The learned literal manager
 **/

#include "preprocessing/learned_literal_manager.h"

#include "preprocessing/assertion_pipeline.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"

namespace cvc5 {
namespace preprocessing {

LearnedLiteralManager::LearnedLiteralManager(PreprocessingPassContext* pcontext,
                                             context::UserContext* u,
                                             ProofNodeManager* pnm)
    : d_pcontext(pcontext), d_topLevelSubstitutions(u, pnm), d_learnedLits(u)
{
}

void LearnedLiteralManager::notifyLearnedLiteral(Node lit)
{
  d_learnedLits.insert(lit);
  Trace("pp-llm") << "LLM:notifyLearnedLiteral: " << lit << std::endl;
}

std::vector<Node>& LearnedLiteralManager::getLearnedLiterals()
{
  // refresh the set of learned literals
  d_currLearnedLits.clear();
  for (NodeSet::const_iterator it = d_learnedLits.begin(),
                               itEnd = d_learnedLits.end();
       it != itEnd;
       ++it)
  {
    // update based on substitutions
    Node tlsNode = d_topLevelSubstitutions.get().apply(*it);
    tlsNode = theory::Rewriter::rewrite(tlsNode);
    d_currLearnedLits.push_back(tlsNode);
    Trace("pp-llm") << "Learned literal : " << tlsNode << " from " << (*it) << std::endl;
  }
  return d_currLearnedLits;
}

theory::TrustSubstitutionMap& LearnedLiteralManager::getTopLevelSubstitutions()
{
  return d_topLevelSubstitutions;
}

}  // namespace preprocessing
}  // namespace cvc5
