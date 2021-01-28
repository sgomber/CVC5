/*********************                                                        */
/*! \file shared_solver_central.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Shared solver in the centralized architecture.
 **/

#include "theory/shared_solver_central.h"

#include "theory/quantifiers_engine.h"
#include "theory/shared_terms_database.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

SharedSolverCentral::SharedSolverCentral(TheoryEngine& te,
                                         ProofNodeManager* pnm)
    : SharedSolver(te, pnm), d_centralEe(nullptr)
{
}

bool SharedSolverCentral::needsEqualityEngine(theory::EeSetupInfo& esi)
{
  // need an equality engine but don't need notifications
  return true;
}

void SharedSolverCentral::setEqualityEngine(eq::EqualityEngine* ee)
{
  d_centralEe = ee;
}

void SharedSolverCentral::preRegisterSharedInternal(TNode t)
{
  // TODO?
}

EqualityStatus SharedSolverCentral::getEqualityStatus(TNode a, TNode b)
{
  if (d_centralEe->hasTerm(a) && d_centralEe->hasTerm(b))
  {
    // Check for equality (simplest)
    if (d_centralEe->areEqual(a, b))
    {
      // The terms are implied to be equal
      return EQUALITY_TRUE;
    }
    // Check for disequality
    if (d_centralEe->areDisequal(a, b, false))
    {
      // The terms are implied to be dis-equal
      return EQUALITY_FALSE;
    }
  }
  // otherwise, ask the theory
  return d_te.theoryOf(Theory::theoryOf(a.getType()))->getEqualityStatus(a, b);
}

void SharedSolverCentral::assertSharedEquality(TNode equality,
                                               bool polarity,
                                               TNode reason)
{
  Trace("shared-solver") << "assertSharedEquality (central): " << equality
                         << " " << polarity << " " << reason << std::endl;
  d_centralEe->assertEquality(equality, polarity, reason);
}

TrustNode SharedSolverCentral::maybeExplain(TNode lit)
{
  // does it hold in the central equality engine?
  bool polarity = lit.getKind() != kind::NOT;
  TNode atom = polarity ? lit : lit[0];
  std::vector<TNode> assumps;
  if (atom.getKind() == kind::EQUAL)
  {
    if (!d_centralEe->hasTerm(atom[0]) || !d_centralEe->hasTerm(atom[1]))
    {
      return TrustNode::null();
    }
    if (polarity ? d_centralEe->areEqual(atom[0], atom[1])
                 : d_centralEe->areDisequal(atom[0], atom[1], true))
    {
      d_centralEe->explainEquality(atom[0], atom[1], polarity, assumps);
    }
  }
  else if (!d_centralEe->hasTerm(atom))
  {
    return TrustNode::null();
  }
  else
  {
    TNode atomRep = d_centralEe->getRepresentative(atom);
    if (atomRep.isConst() && atomRep.getConst<bool>() == polarity)
    {
      d_centralEe->explainPredicate(atom, polarity, assumps);
    }
    else
    {
      return TrustNode::null();
    }
  }
  Assert(!assumps.empty());
  NodeManager* nm = NodeManager::currentNM();
  Node exp =
      assumps.size() == 1 ? Node(assumps[0]) : nm->mkNode(kind::AND, assumps);
  return TrustNode::mkTrustPropExp(lit, exp, nullptr);
}

TrustNode SharedSolverCentral::explain(TNode literal, TheoryId id)
{
  // first, try to explain with the central equality engine
  if (id == THEORY_BUILTIN)
  {
    TrustNode texp = maybeExplain(literal);
    if (!texp.isNull())
    {
      Trace("shared-solver")
          << "\tTerm was explained by the central equality engine"
          << texp.getNode() << std::endl;
      return texp;
    }
  }
  if (id == THEORY_BUILTIN)
  {
    // explanation based on the specific solver
    Unhandled() << "SharedSolverCentral::explain: expected literal propagated "
                   "by THEORY_BUILTIN to hold in the central equality engine: "
                << literal;
  }
  // HACK: ignore the tracking from theory engine (id input to this method)
  // id = Theory::theoryOf(literal);
  Theory* t = d_te.theoryOf(id);
  AlwaysAssert(t != nullptr)
      << "Asking to explain literal from theory that does not exist?";
  // Otherwise, use theoryOf ?
  // By default, we ask the individual theory for the explanation.
  // It is possible that a centralized approach could preempt this.
  TrustNode texp = t->explain(literal);
  Trace("shared-solver") << "\tTerm was propagated by owner theory: " << id
                         << ". Explanation: " << texp.getNode() << std::endl;
  return texp;
}

}  // namespace theory
}  // namespace CVC4
