/*********************                                                        */
/*! \file inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An inference manager for Theory
 **/

#include "theory/inference_manager.h"

#include "theory/uf/equality_engine.h"
#include "theory/theory.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

InferManager::InferManager(Theory& t, TheoryState& state)
    : d_theory(t), d_state(state), d_out(t.getOutputChannel()), d_ee(nullptr), d_pnm(nullptr)
{

}

void InferManager::setEqualityEngine(eq::EqualityEngine* ee) { d_ee = ee; }

void InferManager::conflictEqConstantMerge(TNode a, TNode b)
{
  if (!d_state.isInConflict())
  {
    TrustNode tconf = mkTrustedConflictEqConstantMerge(a, b);
    trustedConflict(tconf);
  }
}

void InferManager::conflict(TNode conf)
{
  if (!d_state.isInConflict())
  {
    TrustNode tconf = mkTrustedConflict(conf);
    trustedConflict(tconf);
  }
}

void InferManager::trustedConflict(TrustNode tconf)
{
  if (!d_state.isInConflict())
  {
    d_state.notifyInConflict();
    d_out.trustedConflict(tconf);
  }
}

bool InferManager::propagate(TNode lit)
{
  // If already in conflict, no more propagation
  if (d_state.isInConflict())
  {
    return false;
  }
  // Propagate out
  bool ok = d_out.propagate(lit);
  if (!ok)
  {
    d_state.notifyInConflict();
  }
  return ok;
}

TrustNode InferManager::explain(TNode lit)
{
  // TODO: use proof equality engine if it exists
  if (d_ee != nullptr)
  {
    Node exp = mkExplain(lit);
    return TrustNode::mkTrustPropExp(lit, exp, nullptr);
  }
  Unimplemented() << "Theory " << d_theory.getId()
                  << " sent a conflict but doesn't implement the "
                     "Theory::explain() interface!";
}

TrustNode InferManager::mkTrustedConflictEqConstantMerge(TNode a, TNode b)
{
  // TODO: use proof equality engine if it exists
  if (d_ee != nullptr)
  {
    Node lit = a.eqNode(b);
    Node conf = mkExplain(lit);
    return TrustNode::mkTrustConflict(conf, nullptr);
  }
  Unimplemented() << "Theory " << d_theory.getId()
                  << " mkTrustedConflictEqConstantMerge";
}

TrustNode InferManager::mkTrustedConflict(TNode conf)
{
  // TODO: use proof equality engine if it exists
  // TODO
  Unimplemented() << "Theory " << d_theory.getId() << " mkTrustedConflict";
}

Node InferManager::mkExplain(TNode lit) const
{
  std::vector<TNode> assumptions;
  explain(lit, assumptions);
  Node ret;
  NodeManager* nm = NodeManager::currentNM();
  if (assumptions.empty())
  {
    ret = nm->mkConst(true);
  }
  else if (assumptions.size() == 1)
  {
    ret = assumptions[0];
  }
  else
  {
    ret = nm->mkNode(kind::AND, assumptions);
  }
  return ret;
}

void InferManager::explain(TNode lit, std::vector<TNode>& assumptions) const
{
  Assert(d_ee != nullptr);
  bool polarity = lit.getKind() != NOT;
  TNode atom = polarity ? lit : lit[0];
  std::vector<TNode> tassumptions;
  if (atom.getKind() == EQUAL)
  {
    if (atom[0] != atom[1])
    {
      Assert(d_ee->hasTerm(atom[0]));
      Assert(d_ee->hasTerm(atom[1]));
      d_ee->explainEquality(atom[0], atom[1], polarity, tassumptions);
    }
  }
  else
  {
    d_ee->explainPredicate(atom, polarity, tassumptions);
  }
  for (const TNode a : tassumptions)
  {
    if (std::find(assumptions.begin(), assumptions.end(), a)
        == assumptions.end())
    {
      assumptions.push_back(a);
    }
  }
}

void InferManager::assertInternalFact(TNode atom, bool pol, TNode fact)
{
  Assert (d_ee!=nullptr);
  if (atom.getKind() == kind::EQUAL)
  {
    d_ee->assertEquality(atom, pol, fact);
  }
  else
  {
    d_ee->assertPredicate(atom, pol, fact);
  }
  // call the notify fact method, where this is an internally generated fact
  d_theory.notifyFact(atom, pol, fact, true);
}

}  // namespace theory
}  // namespace CVC4
