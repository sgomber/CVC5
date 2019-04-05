/*********************                                                        */
/*! \file inst_explain_db.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Instantiate explain database utility
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_DB_H
#define __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_DB_H

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

enum ExplainStatus
{
  EXP_STATUS_FULL,
  EXP_STATUS_INCOMPLETE,
  EXP_STATUS_FAIL
};

class InstExplainDb
{
 public:
  InstExplainDb(QuantifiersEngine* qe);
  /** reset */
  void reset(Theory::Effort e);
  /** register explanations
   *
   * This initializes all explanation information relevant for the instantiation
   * lemma ilem.
   *
   * ilem is the rewritten form of ( ~q V n ),
   * n is the substituted body of the quantified formula such that
   *  ( n * { q.vars -> ts } ) = q[1],
   * q is the quantified formula formula,
   * ts are the terms we have instantiated with.
   */
  void registerExplanation(Node ilem, Node n, Node q, std::vector<Node>& ts);
  /** get instantiation explain */
  InstExplainLit& getInstExplainLit(Node lit);
  InstExplainInst& getInstExplainInst(Node inst);

  /** explain */
  ExplainStatus explain(Node q,
                        const std::vector<Node>& terms,
                        std::map<Node, eq::EqProof>& expPf,
                        EqExplainer* eqe,
                        std::vector<Node>& lems,
                        bool regressInst,
                        const char* ctx);

 private:
  /** pointer to the quantifiers engine */
  QuantifiersEngine* d_qe;
  /** evaluator utility */
  IeEvaluator d_ev;
  /** common constants */
  Node d_true;
  Node d_false;
  // FIXME TEMPORARY
  bool d_doExit;
  /** map from literal to possible explanations */
  std::map<Node, InstExplainLit> d_lit_explains;
  /** map from instantiate lemma to explanation objects */
  std::map<Node, InstExplainInst> d_inst_explains;
  /** activated */
  std::map<Node, bool> d_active_lexp;
  /** waiting list
   *
   * Maps literals to the instantiation lemmas that currently propagate them.
   */
  std::map<Node, std::vector<Node> > d_waiting_prop;
  /** activated instantiations */
  std::map<Node, bool> d_active_inst;

  void activateLit(Node lit);
  void activateInst(Node inst, Node srcLit, InstExplainLit& src);
  Node d_null;
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
  Node generalize(eq::EqProof* eqp,
                  std::map<eq::EqProof*, Node>& concs,
                  std::map<eq::EqProof*, std::map<Node, GLitInfo> >& concsg,
                  unsigned tb = 0);
  bool getMatchIndex(Node eq, Node n, unsigned& index);
  /** convert to equality from arbitrary predicate n */
  Node convertEq(Node n);
  /** convert to non-equality (inverse of above for rewritten nodes) */
  Node convertRmEq(Node n);

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
  bool instExplain(
      GLitInfo& g, Node olit, Node lit, Node inst, const char* c, unsigned tb);
  /** indent tb tabulations on trace c. */
  static void indent(const char* c, unsigned tb);

  static bool isGeneralization(Node n, Node gn);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_DB_H */
