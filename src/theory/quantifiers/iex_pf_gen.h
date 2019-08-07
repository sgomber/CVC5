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
#include "theory/quantifiers/iex_proof.h"
#include "theory/quantifiers/inst_explain.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

class InstExplainDb;

/** Instantiation explain proof generator
 *
 * This class implements the main algorithms of the instiation explantaion
 * inference system.
 *
 */
class InstExplainPfGen
{
 public:
  InstExplainPfGen(InstExplainDb& parent, QuantifiersEngine* qe);
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
  /** Generalize
   *
   * This recursively computes a generalization of proof eqp, stored in g, so
   * that it is a proof of tgtLit. This method returns true if we succeeded.
   *
   * reqPureGen: if this flag is true, we require that g is a purely general,
   * that is, a proof with no open leaves.
   *
   * tb is the tabulation level (for debugging).
   */
  bool generalize(IexOutput& iout,
                  Node tgtLit,
                  eq::EqProof* eqp,
                  IexProof& g,
                  bool reqPureGen,
                  unsigned tb = 0);

  /** reset */
  void reset(Theory::Effort e);

 private:
  /** pointer to parent object */
  InstExplainDb& d_ied;
  /** pointer to the quantifiers engine */
  QuantifiersEngine* d_qe;
  /** virtual model utility */
  VirtualModel* d_vmodel;
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
  /** generalize internal
   *
   * A helper function for generalize. This computes a proof generalization
   * for eqp. We return the node corresponding to the (ground) conclusion of
   * eqp.
   *
   * tgtLit: The target generalized conclusion we wish to generalize the proof
   * eqp to prove. This may be null if we do not know what we are generalizing.
   *
   * eqp: The (ground UF) proof we are generalizing.
   *
   * g: The generalized proof we are constructing.
   *
   * concs: caches the concrete conclusion computed for each proof
   * node visited in recursive calls.
   *
   * reqPureGen: if this flag is true, we require that the generalized proof
   * of tgtLit is purely general.
   *
   * genPath: the current (ground) literals that are parents of our current
   * path in the proof tree.
   *
   * genSuccess: We set this flag to true if we succeeded in generalizing the
   * proof of eqp to prove tgtLit, or if tgtLit is null.
   *
   * tb is the tabulation level (for debugging).
   */
  Node generalizeInternal(IexOutput& iout,
                          Node tgtLit,
                          eq::EqProof* eqp,
                          IexProof& g,
                          std::map<eq::EqProof*, Node>& concs,
                          bool reqPureGen,
                          std::map<Node, bool>& genPath,
                          bool& genSuccess,
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
  bool instExplain(IexOutput& iout,
                   IexProof& g,
                   Node olit,
                   Node lit,
                   Node inst,
                   std::map<Node, bool>& genPath,
                   bool reqPureGen,
                   const char* c,
                   unsigned tb);
  /** find instantiation explanation for opl/pl
   *
   * This finds a generalizing proof of opl, possibly with a UPG (a unique open
   * leaf) if reqPureGen is false.
   *
   * The outcome of this call is one of three cases:
   * 1. (PURELY GENERAL) The assumptions of g are appended with sufficient
   * assumptions for showing a purely general proof of opl. Return true.
   * 2. (UPG) The subproof g.d_conclusions[pl][opl] is populated with one with
   * a UPG whose conclusion is opl. Return true.
   * 3. (FAIL) g is unmodified. Return false.
   */
  bool instExplainFind(IexOutput& iout,
                       IexProof& g,
                       Node opl,
                       Node pl,
                       Node inst,
                       std::map<Node, bool>& genPath,
                       bool reqPureGen,
                       const char* c,
                       unsigned tb);

  /** indent tb tabulations on trace c. */
  static void indent(const char* c, unsigned tb);
  /** returns true if gn is a generalization of n */
  static bool isGeneralization(Node n, Node gn);

  /** cache of instExplainFind */
  std::map<Node, Node> d_instFindPure;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_DB_H */
