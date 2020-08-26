/*********************                                                        */
/*! \file inference_manager_buffered.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A buffered inference manager
 **/

#include "theory/inference_manager_buffered.h"

#include "theory/theory.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

InferenceManagerBuffered::InferenceManagerBuffered(Theory& t,
                  TheoryState& state,
                  ProofNodeManager* pnm) : TheoryInferenceManager(t, state, pnm)
                  {
                    
                  }
                  
bool InferenceManagerBuffered::hasProcessed() const
{
  return d_theoryState.isInConflict() || !d_pendingLem.empty() || !d_pendingFact.empty();
}

bool InferenceManagerBuffered::hasPendingFact() const
{
  return !d_pendingFact.empty();
}

bool InferenceManagerBuffered::hasPendingLemma() const
{
  return !d_pendingLem.empty();
}

void InferenceManagerBuffered::addPendingLemma(Node lem,
                           LemmaProperty p)
{
  d_pendingLem.push_back(std::pair<Node, LemmaProperty>(lem,p));
}

void InferenceManagerBuffered::addPendingFact(Node fact, Node exp, bool asLemma)
{
  if (!asLemma)
  {
    Assert (fact.getKind()!=AND && fact.getKind()!=OR);
    d_pendingFact.push_back(std::pair<Node, Node>(fact,exp));
    return;
  }
  // TODO: explain with equality engine
}

void InferenceManagerBuffered::doPendingFacts()
{
  size_t i = 0;
  while (!d_theoryState.isInConflict() && i < d_pendingFact.size())
  {    
    std::pair<Node, Node>& pfact = d_pendingFact[i];
    Node fact = pfact.first;
    Node exp = pfact.second;
    bool polarity = fact.getKind() != NOT;
    TNode atom = polarity ? fact : fact[0];
    // if we don't process it
    if (!preNotifyPendingFact(atom, polarity, exp))
    {
      // no double negation or conjunctive conclusions
      Assert(atom.getKind() != NOT && atom.getKind() != AND);
      assertInternalFact(atom, polarity, exp);
    }
    i++;
  }
  d_pendingFact.clear();
}

void InferenceManagerBuffered::doPendingLemmas()
{
  // process all the pending lemmas
  for (const std::pair<Node, LemmaProperty>& plem : d_pendingLem)
  {
    if (preNotifyPendingLemma(plem.first, plem.second))
    {
      // processed it internally
      continue;
    }
    // send lemma, not cached
    d_out.lemma(plem.first, plem.second);
  }
  d_pendingLem.clear();
}

bool preNotifyPendingFact(TNode atom, bool pol, TNode fact)
{
  return false;
}

bool preNotifyPendingLemma(TNode lem, LemmaProperty p)
{
  return false;
}

}  // namespace theory
}  // namespace CVC4
