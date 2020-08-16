/*********************                                                        */
/*! \file solver_state.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A solver state for Theory
 **/

#include "theory/solver_state.h"

#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {

SolverState::SolverState(context::Context* c, context::UserContext* u, Valuation val) : d_context(c), d_ucontext(u), d_valuation(val), d_ee(nullptr),
      d_conflict(c, false)
{
  
}

void SolverState::finishInit(eq::EqualityEngine* ee)
{
  d_ee = ee;
}

context::Context* SolverState::getSatContext() const
{
  return d_context;
}

context::UserContext* SolverState::getUserContext() const
{
  return d_ucontext;
}

Node SolverState::getRepresentative(Node t) const
{
  Assert(d_ee!=nullptr);
  if (d_ee->hasTerm(t))
  {
    return d_ee->getRepresentative(t);
  }
  return t;
}

bool SolverState::hasTerm(Node a) const
{
  return d_ee->hasTerm(a);
}

bool SolverState::areEqual(Node a, Node b) const
{
  if (a == b)
  {
    return true;
  }
  else if (hasTerm(a) && hasTerm(b))
  {
    return d_ee->areEqual(a, b);
  }
  return false;
}

bool SolverState::areDisequal(Node a, Node b) const
{
  if (a == b)
  {
    return false;
  }
  
  bool isConst = true;
  if (hasTerm(a))
  {
    a = d_ee->getRepresentative(a);
    isConst = a.isConst();
  }
  else if (!a.isConst())
  {
    // not disequal
    return false;
  }
  
  if (hasTerm(b))
  {
    b = d_ee->getRepresentative(b);
    isConst = isConst && b.isConst();
  }
  else if (!b.isConst())
  {
    // not disequal
    return false;
  }
  
  if (isConst)
  {
    // distinct constants are disequal
    return a!=b;
  }
  // otherwise there may be an explicit disequality in the equality engine
  Assert (hasTerm(a) && hasTerm(b));
  return d_ee->areDisequal(ar, br, false);
}

eq::EqualityEngine* SolverState::getEqualityEngine() const
{
  return d_ee;
}

void SolverState::setConflict()
{
  d_conflict = true;
}

bool SolverState::isInConflict() const
{
  return d_conflict;
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
