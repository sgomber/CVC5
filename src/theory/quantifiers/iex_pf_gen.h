/*********************                                                        */
/*! \file iex_pf_gen.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Instantiate explain proof generalization
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__IEX_PF_GEN_H
#define __CVC4__THEORY__QUANTIFIERS__IEX_PF_GEN_H

#include <map>
#include <vector>
#include "expr/node.h"
#include "theory/quantifiers/equality_explain.h"
#include "theory/quantifiers/gen_lit_info.h"
#include "theory/quantifiers/inst_explain.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class InstExplainDb;

class InstExplainPfGen
{
 public:
  InstExplainPfGen(InstExplainDb& parent, QuantifiersEngine* qe);
  /** Generalize
   *
   * This recursively computes a generalization of proof eqp.
   *
   * The map concs stores the concrete conclusion computed for each proof
   * node visited in recursive calls.
   *
   * The map concsg stores (a set of) generalized conclusions for each proof
   * node visited in recursive class. It is the case that each node in the
   * domain of concsg[p] is a generalization of concs[p]. The information
   * in the range of concsg[p][L] for each L contains the "generalized
   * literal information", which contains the necessary information for
   * interpretting L.
   *
   * genPath is the current (ground) literals that are parents of our current
   * path in the proof tree.
   *
   * tb is the tabulation level (for debugging).
   */
  Node generalize(Node tgtLit,
                  eq::EqProof* eqp,
                  std::map<eq::EqProof*, Node>& concs,
                  std::map<eq::EqProof*, GLitInfo>& concsg,
                  unsigned tb = 0);
  /**
   * Regress the explanation of proof sketch eqp using eqe.
   *
   * The leaves of eqp (those with id MERGED_THROUGH_EQUALITY) are expected to
   * be explanable by the explainer utility eqe.
   *
   * This method recursively updates proof eqp so that its leaves are input
   * literals with respect to eqe. If successful, it returns true and adds all
   * assumptions to the vector assumptions.
   *
   * For example, if eqe is based on the equality engine of TheoryUF,
   * then if this method returns true, then the leaves of eqp are input literals
   * belonging to TheoryUF.
   */
  bool regressExplain(EqExplainer* eqe,
                      std::vector<TNode>& assumptions,
                      eq::EqProof* eqp);

  /** reset */
  void reset(Theory::Effort e);

 private:
  /** pointer to parent object */
  InstExplainDb& d_ied;
  /** pointer to the quantifiers engine */
  QuantifiersEngine* d_qe;
  /** evaluator utility */
  IeEvaluator& d_ev;
  /** common constants */
  Node d_true;
  Node d_false;
  Node d_null;

  /**
   * If this method returns true, then eq is an equality such that eq[index]=n.
   */
  static bool getMatchIndex(Node eq, Node n, unsigned& index);
  /** convert to equality from arbitrary predicate n */
  Node convertEq(Node n) const;
  /** convert to non-equality (inverse of above for rewritten nodes) */
  Node convertRmEq(Node n) const;
  /** generalize internal */
  Node generalizeInternal(Node tgtLit,
                          eq::EqProof* eqp,
                          std::map<eq::EqProof*, Node>& concs,
                          std::map<eq::EqProof*, GLitInfo>& concsg,
                          std::map<Node, bool>& genPath,
                          unsigned tb);
  /** Instantiation explanation
   *
   * This is called when the instantiation lemma inst currently propagates the
   * ground literal lit. This method attempts to lift the explanation of lit
   * to a universal conclusion.
   *
   * In detail:
   *   lit is an instance of a literal in quantified formula Q,
   *   inst is an inst lemma Q[x] => Q[c] that is currently propagating lit,
   *   olit is the uninstantiated form of lit, i.e. olit { x -> c } = lit.
   * If this method returns true, then:
   *   assumptions => forall x. olit
   * and assumptions are SAT literals that currently hold in the SAT context.
   *
   * For example if:
   *   olit is P( x )
   *   lit is P( c )
   *   inst is (forall x. P( x ) V Q( x )) => P(c) V Q(c)
   * Assume ~Q(c) and forall x. ~Q(x) are asserted in the current SAT context.
   * Thus, the lemma inst propagates P(c).
   * This method may return true and updates the assumptions of g to:
   *   { forall x. P( x ) V Q( x ), forall x. ~Q( x ) }
   * This can be computed via recursive calls to instExplain, say in the case
   * that an instantiation lemma (forall x. ~Q(x) => ~Q(c)) occurs as a clause
   * in the SAT solver and hence propagates ~Q(c).
   * This corresponds to the (first-order resolution) inference:
   *   forall x. P( x ) V Q( x ) ^ forall x. ~Q( x ) => forall x. P( x ).
   *
   * c is the name of a Trace, and tb is number of tabs (for debug printing).
   */
  bool instExplain(GLitInfo& g,
                   Node olit,
                   Node lit,
                   Node inst,
                   std::map<Node, bool>& genPath,
                   const char* c,
                   unsigned tb);
  /** find instantiation explanation for opl/pl
   */
  bool instExplainFind(GLitInfo& g,
                       Node opl,
                       Node pl,
                       Node inst,
                       std::map<Node, bool>& genPath,
                       const char* c,
                       unsigned tb);

  /** indent tb tabulations on trace c. */
  static void indent(const char* c, unsigned tb);
  /** returns true if gn is a generalization of n */
  static bool isGeneralization(Node n, Node gn);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_DB_H */
