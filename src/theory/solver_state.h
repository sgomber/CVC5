/*********************                                                        */
/*! \file solver_state.h
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

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SOLVER_STATE_H
#define CVC4__THEORY__SOLVER_STATE_H

#include "expr/node.h"
#include "theory/valuation.h"
#include "context/context.h"

namespace CVC4 {
namespace theory {

namespace eq {
  class EqualityEngine;
}
  
class SolverState
{
public:
  SolverState(context::Context* c, context::UserContext* u, Valuation val);
  /**
   * Finish initialize, there ee is a pointer to the official equality engine
   * of theory.
   */
  void finishInit(eq::EqualityEngine* ee);
  /** Get the SAT context */
  context::Context* getSatContext() const;
  /** Get the user context */
  context::UserContext* getUserContext() const;
  //-------------------------------------- equality information
  /** Is t registered as a term in the equality engine of this class? */
  bool hasTerm(Node a) const;
  /**
   * Get the representative of t in the equality engine of this class, or t
   * itself if it is not registered as a term.
   */
  Node getRepresentative(Node t) const;
  /**
   * Are a and b equal according to the equality engine of this class? Also
   * returns true if a and b are identical.
   */
  bool areEqual(Node a, Node b) const;
  /**
   * Are a and b disequal according to the equality engine of this class? Also
   * returns true if the representative of a and b are distinct constants.
   */
  bool areDisequal(Node a, Node b) const;
  /** get equality engine */
  eq::EqualityEngine* getEqualityEngine() const;
  //-------------------------------------- end equality information
  /**
   * Set that the current state of the solver is in conflict. This should be
   * called immediately after a call to conflict(...) on the output channel of
   * the theory.
   */
  void setConflict();
  /** Are we currently in conflict? */
  bool isInConflict() const;
protected:
  /** Pointer to the SAT context object used by the theory. */
  context::Context* d_context;
  /** Pointer to the user context object used by the theory. */
  context::UserContext* d_ucontext;
  /**
   * The valuation proxy for the Theory to communicate back with the
   * theory engine (and other theories).
   */
  Valuation d_valuation;
  /** Pointer to equality engine of the theory. */
  eq::EqualityEngine* d_ee;
  /** Are we in conflict? */
  context::CDO<bool> d_conflict;
};
  

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__SOLVER_STATE_H */
