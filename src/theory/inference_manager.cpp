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

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

InferManager::InferManager(Theory& t, TheoryState& state)
    : d_theory(t),
      d_state(state),
      d_out(t.getOutputChannel()),
      d_ee(nullptr),
      d_pnm(nullptr)
{
}

void InferManager::setEqualityEngine(eq::EqualityEngine* ee) { d_ee = ee; }

void InferManager::conflictEqConstantMerge(TNode a, TNode b)
{
  if (!d_state.isInConflict())
  {
    TrustNode tconf = explainConflictEqConstantMerge(a, b);
    trustedConflict(tconf);
  }
}

void InferManager::conflict(TNode conf)
{
  if (!d_state.isInConflict())
  {
    d_out.conflict(conf);
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

bool InferManager::propagateLit(TNode lit)
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

TrustNode InferManager::explainLit(TNode lit)
{
  // TODO: use proof equality engine if it exists
  if (d_ee != nullptr)
  {
    Node exp = mkExplain(lit);
    return TrustNode::mkTrustPropExp(lit, exp, nullptr);
  }
  Unimplemented() << "Inference manager for " << d_theory.getId()
                  << " was asked to explain a propagation but doesn't have an "
                     "equality engine or implement the "
                     "InferManager::explainLit interface!";
}

TrustNode InferManager::explainConflictEqConstantMerge(TNode a, TNode b)
{
  // TODO: use proof equality engine if it exists
  if (d_ee != nullptr)
  {
    Node lit = a.eqNode(b);
    Node conf = mkExplain(lit);
    return TrustNode::mkTrustConflict(conf, nullptr);
  }
  Unimplemented() << "Inference manager for " << d_theory.getId()
                  << " mkTrustedConflictEqConstantMerge";
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
  Trace("infer-manager") << "InferManager::explain: " << lit << std::endl;
  Assert(d_ee != nullptr);
  bool polarity = lit.getKind() != NOT;
  TNode atom = polarity ? lit : lit[0];
  std::vector<TNode> tassumptions;
  if (atom.getKind() == EQUAL)
  {
    Assert(d_ee->hasTerm(atom[0]));
    Assert(d_ee->hasTerm(atom[1]));    
    if (!polarity)
    {
      // ensure that we are ready to explain the disequality
      AlwaysAssert(d_ee->areDisequal(atom[0], atom[1], true));
    }
    else if (atom[0] == atom[1])
    {
      return;
    }
    d_ee->explainEquality(atom[0], atom[1], polarity, tassumptions);
  }
  else
  {
    d_ee->explainPredicate(atom, polarity, tassumptions);
  }
  // ensure that duplicates are removed
  for (const TNode a : tassumptions)
  {
    if (std::find(assumptions.begin(), assumptions.end(), a)
        == assumptions.end())
    {
      Trace("infer-manager") << "..." << a << std::endl;
      assumptions.push_back(a);
    }
  }
  Trace("infer-manager") << "InferManager::finished explain" << std::endl;
}

void InferManager::assertInternalFact(TNode atom, bool pol, TNode fact)
{
  Assert(d_ee != nullptr);
  Trace("infer-manager") << "InferManager::assertInternalFact: " << fact
                         << std::endl;
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
  Trace("infer-manager") << "InferManager::finished assertInternalFact"
                         << std::endl;
  // TODO: keep set for fact?
}

}  // namespace theory
}  // namespace CVC4
