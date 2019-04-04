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
#include "theory/quantifiers/inst_explain.h"
#include "theory/quantifiers/gen_lit_info.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class EqExplainer
{
 public:
  EqExplainer() {}
  virtual ~EqExplainer() {}
  virtual bool explain(Node lit,
                       std::vector<TNode>& assumptions,
                       eq::EqProof* eqp = nullptr) = 0;

 protected:
  bool explainEe(eq::EqualityEngine* ee,
                 Node lit,
                 std::vector<TNode>& assumptions,
                 eq::EqProof* eqp);
};

class EqExplainerEe : public EqExplainer
{
 public:
  EqExplainerEe(eq::EqualityEngine* ee) : d_ee(ee) {}
  virtual ~EqExplainerEe() {}
  /** explain */
  bool explain(Node lit,
               std::vector<TNode>& assumptions,
               eq::EqProof* eqp = nullptr) override;

 private:
  /** the equality engine */
  eq::EqualityEngine* d_ee;
};

class EqExplainerTe : public EqExplainer
{
 public:
  EqExplainerTe(TheoryEngine* te) : d_te(te) {}
  virtual ~EqExplainerTe() {}
  /** explain */
  bool explain(Node lit,
               std::vector<TNode>& assumptions,
               eq::EqProof* eqp = nullptr) override;

 private:
  /** the theory engine */
  TheoryEngine* d_te;
};

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
                        const std::vector< Node >& terms,
                        const std::vector<Node>& exp,
                        const std::vector<Node>& gexp,
                        EqExplainer* eqe,
                        std::vector<Node>& rexp,
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

  /** instantiate explain */
  void instLitExplain(Node lit,
                      std::map<Node, bool>& expres,
                      std::map<Node, bool>& expresAtom,
                      bool regressInst);
  void instExplain(Node n,
                   std::map<Node, bool>& expres,
                   std::map<Node, bool>& expresAtom,
                   bool regressInst);
  void instBoolExplain(Node n,
                   std::map<Node, bool>& expres,
                   std::vector< Node >& lits);
  Node d_null;
  Node generalize(Node e,
                  Node ge,
                  eq::EqProof* eqp,
                  std::map<eq::EqProof*, Node>& concs,
                  std::map<eq::EqProof*, std::map<Node, GLitInfo> >& concsg,
                  unsigned tb = 0);
  bool getMatchIndex(Node eq, Node n, unsigned& index);
  /** convert to equality from arbitrary predicate n */
  Node convertEq(Node n);
  /** convert to non-equality (inverse of above for rewritten nodes) */
  Node convertRmEq(Node n);

  static void indent(const char* c, unsigned tb);
  
  static bool isGeneralization(Node n, Node gn );
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_DB_H */
