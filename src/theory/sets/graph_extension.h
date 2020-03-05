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
#include "theory/sets/inference_manager.h"
#include "theory/sets/solver_state.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {

class GraphInfo
{
public:
  
};
  
/** The graph extension of the theory of sets
 *
 * This class implements inference schemes described in Meng et al. CADE 2017
 * for handling quantifier-free constraints in the theory of relations.
 *
 * In CVC4, relations are represented as sets of tuples. The theory of
 * relations includes constraints over operators, e.g. TRANSPOSE, JOIN and so
 * on, which apply to sets of tuples.
 *
 * Since relations are a special case of sets, this class is implemented as an
 * extension of the theory of sets. That is, it shares many components of the
 * TheorySets object which owns it.
 */
class GraphExtension {
public:
 GraphExtension(SolverState& s,
                InferenceManager& im,
                eq::EqualityEngine& e,
                context::Context* c,
                context::UserContext* u);
 ~GraphExtension();
 /**
  * Called when a node is pre-registered to the theory of sets.
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
  Node                          d_true;
  Node                          d_false;
  /** Reference to the state object for the theory of sets */
  SolverState& d_state;
  /** Reference to the inference manager for the theory of sets */
  InferenceManager& d_im;
  /** Reference to the equality engine of theory of sets */
  eq::EqualityEngine& d_ee;
  /** Information for each graph (binary relation) */
  std::map<Node,GraphInfo> d_ginfo;
};

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__SETS__GRAPH_EXTENSION_H */
