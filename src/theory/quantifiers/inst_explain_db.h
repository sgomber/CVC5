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
#include "theory/quantifiers/iex_pf_gen.h"
#include "theory/quantifiers/inst_explain.h"
#include "theory/quantifiers/subsume.h"
#include "theory/quantifiers/term_database.h"
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
  friend class InstExplainPfGen;

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
  /** the term database of d_qe */
  TermDb* d_tdb;
  /** the subsume utility of d_qe */
  Subsume* d_subsume;
  /** evaluator utility */
  IeEvaluator d_ev;
  /** the instantiate explain proof generalization utility */
  InstExplainPfGen d_iexpfg;
  /** common constants */
  Node d_true;
  Node d_false;
  Node d_null;
  /** have we seen an instantiation of this quantified formula? */
  std::map<Node, bool> d_quants;
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
  std::map<Node, std::vector<std::pair<Node, Node>>> d_waiting_prop;
  /** activated instantiations */
  std::map<Node, bool> d_active_inst;
  /** get explain information for literal lit */
  InstExplainLit& getInstExplainLit(Node lit);
  /** find explain information for literal lit
   *
   * Returns true if its information exists in this class and updates the
   * iterator, returns false otherwise.
   */
  bool findInstExplainLit(Node lit,
                          std::map<Node, InstExplainLit>::iterator& itl);
  /** get explain information for instantiation lemma inst */
  InstExplainInst& getInstExplainInst(Node inst);
  /** activate the literal lit
   *
   * This computes the set of instantiation lemmas that currently propagate it.
   * It does so by calling activateInst for each instantiation lemma that may
   * propagate it.
   */
  void activateLit(Node lit);
  /** activate instantiation lemma
   *
   * This computes the literals that instantiation lemma inst currently
   * propagates. The literal srcLit is the literal that was interested in
   * whether inst propagated it.
   */
  void activateInst(Node inst, Node srcLit, InstExplainLit& src);
  /**
   * If this method returns true, then eq is an equality such that eq[index]=n.
   */
  static bool getMatchIndex(Node eq, Node n, unsigned& index);
  /** convert to equality from arbitrary predicate n */
  Node convertEq(Node n) const;
  /** convert to non-equality (inverse of above for rewritten nodes) */
  Node convertRmEq(Node n) const;

  /** indent tb tabulations on trace c. */
  static void indent(const char* c, unsigned tb);
  /** returns true if gn is a generalization of n */
  static bool isGeneralization(Node n, Node gn);

  /** Register propagating literal
   *
   * TODO
   */
  void registerPropagatingLiteral(Node olit, Node q);
  /** get symbol index */
  bool getLitSymbolIndex(Node n, Node& f, Node& g, bool& pol) const;
  /** propagating literal cache */
  std::map<Node, std::map<Node, std::map<bool, std::vector<Node>>>> d_plit_map;

  /** conclusion cache
   * 
   * Maps (antecendants, conclusion bodys) to the quantified conclusion of
   * a generalized resolution (GEN-RES) step.
   * 
   * This cache ensures that we do not infer alpha-equivalent quantified
   * formulas in the case where we repeat the same proof generalization.
   * 
   * Notice that repeated proof generalizations ideally don't happen, since
   * the quantified conclusion of the previous generalization could have
   * directly generated a conflicting instance itself. Regardless, we guard
   * this case and do not do a GEN-RES step, and instead do the generalized
   * conflicting instance only using the existing quantified formula stored
   * here.
   */
  std::map<Node, std::map<Node, Node>> d_conc_cache;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_DB_H */
