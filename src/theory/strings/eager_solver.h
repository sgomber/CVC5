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

#include "context/cdhashset.h"
#include "expr/node.h"
#include "options/strings_options.h"
#include "theory/strings/eqc_info.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/solver_state.h"

namespace CVC4 {
namespace theory {
namespace strings {

enum class EagerInfoType : uint32_t
{
  // we have inferred a (complete) constant
  CONSTANT,
  // we have inferred a constant prefix
  PREFIX,
  // we have inferred a constant suffix
  SUFFIX
};

/**
 * Eager solver, which is responsible for tracking of eager information and
 * reporting conflicts to the solver state.
 *
 * Checks for each equivalence class E:
 * (1) Largest prefix is compatible (including constants),
 * (2) Largest suffix is compatible,
 * (3) If E contains a constant,
 */
class EagerSolver
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  EagerSolver(SolverState& state,
              InferenceManager& im,
              options::StringsEagerSolverMode m);
  ~EagerSolver();
  /** called when a new equivalence class is created */
  void eqNotifyNewClass(TNode t);
  /** called when two equivalence classes merge */
  void eqNotifyMerge(TNode t1, TNode t2);
  void eqNotifyPreMerge(TNode t1, TNode t2);
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
  void addEndpointsToEqcInfo(TNode r,
                             TNode t,
                             TNode concat,
                             const std::vector<Node>& exp);
  /** 
   * Add best content, where f is application term in the equivalence class with
   * representative r. This makes the appropriate inference based on the result
   * of getBestContent(f). In particular:
   * 
   * (1) if getBestContent(f) is a constant, we add f = getBestContent(f) as a
   * pending inference with the given explanation,
   * (2) if getBestContent(f) is a contenation term, we record prefix/suffix
   * information based on it,
   * (3) ignore it in all other cases.
   */
  bool inferBestContent(TNode f, TNode r);
  /**
   * Get best content for term f, returns a term fc such that
   *   exp |= f = fc
   * where exp holds in the equality engine.
   */
  Node getBestContent(TNode f, std::vector<Node>& exp);
  /** Get best content for argument term */
  Node getBestContentArg(TNode t, std::vector<Node>& exp);
  /** Get prefix */
  // Node getPrefixRec(Node f, std::vector<Node>& exp, bool isSuf);
  /**
   * Called when equivalence class r is merging into constant c.
   */
  Node processConstantMerges(Node r, Node c);
  /** is k a kind we are doing congruence over? */
  bool isFunctionKind(Kind k) const;
  /** The null node */
  Node d_null;
  /** Reference to the solver state */
  SolverState& d_state;
  /** The (custom) output channel of the theory of strings */
  InferenceManager& d_im;
  /** Mode of the solver */
  options::StringsEagerSolverMode d_mode;
  /** TODO? Terms that evaluate to the constant in their equivalence class */
  NodeSet d_mcTerms;
  /** the use list to process */
  std::set<TNode> d_useList;
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__EAGER_SOLVER_H */
