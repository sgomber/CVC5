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
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"
#include "theory/quantifiers/inst_explain.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class EqExplainer
{
 public:
  EqExplainer() {}
  virtual ~EqExplainer() {}
  virtual bool explain(Node lit, std::vector<TNode>& assumptions) = 0;

 protected:
  bool explainEe(eq::EqualityEngine* ee,
                 Node lit,
                 std::vector<TNode>& assumptions);
};

class EqExplainerEe : public EqExplainer
{
 public:
  EqExplainerEe(eq::EqualityEngine* ee) : d_ee(ee) {}
  virtual ~EqExplainerEe() {}
  /** explain */
  bool explain(Node lit, std::vector<TNode>& assumptions) override;

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
  bool explain(Node lit, std::vector<TNode>& assumptions) override;

 private:
  /** the theory engine */
  TheoryEngine* d_te;
};

enum ExplainStatus 
{
  EXP_STATUS_FULL,
  EXP_STATUS_INCOMPLETE
};
  
class InstExplainDb
{
 public:
  InstExplainDb(QuantifiersEngine * qe);
  /** reset */
  void reset(Theory::Effort e);
  /** register explanations */
  void registerExplanation(Node ilem, Node n);
  /** get instantiation explain */
  InstExplainLit& getInstExplainLit(Node lit);
  InstExplainInst& getInstExplainInst(Node inst);
  
  /** explain */
  ExplainStatus explain(const std::vector<Node>& exp,
               EqExplainer* eqe,
               std::vector<Node>& rexp,
               const char* ctx);

 private:
  /** pointer to the quantifiers engine */
  QuantifiersEngine* d_qe;
  /** common constants */
  Node d_true;
  Node d_false;
  /** map from literal to possible explanations */
  std::map<Node, InstExplainLit> d_lit_explains;
  /** map from instantiate lemma to explanation objects */
  std::map<Node, InstExplainInst> d_inst_explains;
  /** activated */
  std::map< Node, bool > d_active_lexp;
  /** waiting list 
   * 
   * Maps literals to the instantiation lemmas that currently propagate them.
   */
  std::map< Node, std::vector< Node > > d_waiting_prop;
  /** activated instantiations */
  std::map< Node, bool > d_active_inst;
  
  void activateLit(Node lit);
  void activateInst(Node inst, Node srcLit, InstExplainLit& src);

  /** add exp result */
  void insertExpResult(Node exp,
                       std::map<Node, bool>& expres,
                       std::map<Node, bool>& expresAtom);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_DB_H */
