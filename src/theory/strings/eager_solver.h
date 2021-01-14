/*********************                                                        */
/*! \file eager_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The eager solver
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__EAGER_SOLVER_H
#define CVC4__THEORY__STRINGS__EAGER_SOLVER_H

#include <map>

#include "expr/node.h"
#include "theory/strings/eqc_info.h"
#include "theory/strings/solver_state.h"
#include "options/strings_options.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * Eager solver, which is responsible for tracking of eager information and
 * reporting conflicts to the solver state.
 */
class EagerSolver
{
 public:
  EagerSolver(SolverState& state, options::StringsEagerSolverMode m);
  ~EagerSolver();
  /** called when a new equivalence class is created */
  void eqNotifyNewClass(TNode t);
  /** called when two equivalence classes merge */
  void eqNotifyMerge(TNode t1, TNode t2);
  /** called when two equivalence classes are made disequal */
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
  /** notify fact, called when a fact is asserted to theory of strings */
  void notifyFact(TNode atom, bool polarity, TNode fact, bool isInternal);

 private:
  /** add endpoints to eqc info
   *
   * This method is called when term exp is the explanation for why equivalence
   * class r containing t may have a constant endpoint due to a concatentation
   * term concat. For example, we may call this method on:
   *   t := (str.++ x y), concat := (str.++ x y), exp := true
   * where r is representative of t. Another example is:
   *   t := z, concat := (re.++ u w), exp := (str.in.re z (re.++ u w))
   * where r is representative of t.
   */
  void addEndpointsToEqcInfo(Node r, Node t, Node concat, Node exp);
  /**
   * Get best content for term f(t1, ..., tn).
   */
  Node getBestContent(Node f, std::vector<Node>& exp);
  /** Get best content for argument term */
  Node getBestContentArg(Node t, std::vector<Node>& exp);
  /** 
   * Check whether there is a conflict with t having prefix/suffix/containment
   * in c, recursively.
   */
  Node checkConflict(Node t, Node c);
  /** The null node */
  Node d_null;
  /** Reference to the solver state */
  SolverState& d_state;
  /** Mode of the solver */
  options::StringsEagerSolverMode d_mode;
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__EAGER_SOLVER_H */
