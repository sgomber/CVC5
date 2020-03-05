/*********************                                                        */
/*! \file graph_extension.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An extension of the sets theory that specializes in finite graphs.
 **/

#ifndef CVC4__THEORY__SETS__GRAPH_EXTENSION_H
#define CVC4__THEORY__SETS__GRAPH_EXTENSION_H

#include "context/context.h"
#include "expr/node.h"
#include "theory/sets/graph_info.h"
#include "theory/sets/inference_manager.h"
#include "theory/sets/solver_state.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {

/** The graph extension of the theory of sets
 *
 * This extension is intended to handle atoms of the form:
 * (1) (c1, c2) in R, where c1, c2 are constants and R is a binary relation,
 * (2) (c1, c2) in tclosure(R), where c1, c2 are constants and R is a
 * binary relation,
 * (3) R subset ((c1, d1) union ... union (cn, dn)) where c1 ... cn and
 * d1 ... dn are constants.
 */
class GraphExtension
{
 public:
  GraphExtension(SolverState& s,
                 InferenceManager& im,
                 eq::EqualityEngine& e,
                 context::Context* c,
                 context::UserContext* u);
  ~GraphExtension();
  /**
   * Called when a node is pre-registered to the theory of sets. This
   * throws a logic exception if the node is unhandled by this module.
   */
  void preRegisterTerm(TNode node);
  /**
   * Called when the (literal) fact is asserted to the theory of sets whose
   * explanation is exp.
   */
  void assertFact(TNode fact, TNode exp);
  /**
   * Invoke the check method with effort level e. At a high level, this class
   * will make calls to TheorySetsPrivate::processInference to assert facts,
   * lemmas, and conflicts. If this class makes no such call, then the current
   * set of assertions is satisfiable with respect to graph constraints.
   */
  void check(Theory::Effort e);

 private:
  /** Commonly used nodes */
  Node d_true;
  Node d_false;
  /** Reference to the state object for the theory of sets */
  SolverState& d_state;
  /** Reference to the inference manager for the theory of sets */
  InferenceManager& d_im;
  /** Reference to the equality engine of theory of sets */
  eq::EqualityEngine& d_ee;
  /** Information for each graph (binary relation) */
  std::map<Node, GraphInfo> d_ginfo;

  /** Collect elements from set */
  void collectElements(TNode val, TNode g);

  //------------------------------------- logic checks
  /** Logic exception if g is not a graph (binary relation) variable */
  void checkGraphVariable(TNode g);
  /** Logic exception if t is not a constant tuple (c1,c2) */
  void checkEdge(TNode c);
  //------------------------------------- end logic checks
};

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SETS__GRAPH_EXTENSION_H */
