/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * State for congruence closure with free variables
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__STATE_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__STATE_H

#include <memory>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/ccfv/eqc_info.h"
#include "theory/quantifiers/ccfv/free_var_info.h"
#include "theory/quantifiers/ccfv/match_eqc_info.h"
#include "theory/quantifiers/ccfv/pattern_term_info.h"
#include "theory/quantifiers/ccfv/quant_info.h"

namespace cvc5 {

namespace expr {
class TermCanonize;
}

namespace theory {
namespace quantifiers {

class QuantifiersState;
class TermDb;

namespace ccfv {

class CongruenceClosureFv;

class State : protected EnvObj
{
  using NodeList = context::CDList<Node>;
  using NodeSet = context::CDHashSet<Node>;
  using NodeBoolMap = context::CDHashMap<Node, bool>;

 public:
  State(Env& env, QuantifiersState& qs, TermDb* tdb);
  /**
   * Reset round, where nquant is the number of quantified formulas
   */
  void resetRound(size_t nquant);
  //---------------quantifiers info
  QuantInfo& initializeQuantInfo(TNode q,
                                 eq::EqualityEngine* ee,
                                 expr::TermCanonize& tc);
  /** Get quantifiers info */
  QuantInfo& getQuantInfo(TNode q);
  //---------------free variable info
  /** Get free variable info */
  FreeVarInfo& getOrMkFreeVarInfo(TNode v);
  FreeVarInfo& getFreeVarInfo(TNode v);
  //---------------pattern term info
  /** Get pattern term info */
  PatTermInfo& getOrMkPatTermInfo(TNode p);
  PatTermInfo& getPatTermInfo(TNode p);
  //---------------match information
  MatchEqcInfo& getMatchEqcInfo(TNode r);
  //---------------equality notifications
  /** Called when equivalence classes t1 and t2 merge. */
  void eqNotifyMerge(TNode t1, TNode t2);
  /**
   * Called when we have determined that pattern p will not merge with any
   * ground equivalence class.
   */
  void notifyPatternSink(TNode p);
  /**
   * Called when it is determined what pattern p is equal to.
   *
   * If g is not sunk, then g is the (ground) equivalence class that pattern p
   * is equal to. If g is the sink, then we have determined that p will *never*
   * merge into a ground equivalence class in this context.
   */
  void notifyPatternEqGround(TNode p, TNode g);
  //---------------queries
  /** Is finished */
  bool isFinished() const;
  /**
   * Get value for pattern or ordinary term p. This is either a ground
   * represenative, or the sink, or the null node if p is active.
   */
  TNode getValue(TNode p) const;
  /** Get sink node */
  Node getSink() const;
  /** Is sink */
  bool isSink(TNode n) const;
  /** Get ground equivalence classes */
  const std::unordered_set<TNode>& getGroundEqcFor(TypeNode tn) const;
  /** Is ground eqc? */
  bool isGroundEqc(TNode r) const;
  /** Get the ground representative */
  TNode getGroundRepresentative(TNode n) const;
  /** Is quantifier active? */
  bool isQuantActive(TNode q) const;
  /** Set quantified formula inactive */
  void setQuantInactive(QuantInfo& qi);

  /** debugging */
  std::string toStringDebug() const;
  std::string toStringDebugSearch() const;
 private:
  /** Get equivalence class info */
  EqcInfo* getOrMkEqcInfo(TNode r, bool doMk = false);
  /** Get equivalence class info, or nullptr if it does not exist */
  const EqcInfo* getEqcInfo(TNode r) const;
  /**
   * Notify that child was assigned value val, set eq if possible.
   * Return true if we set eq during this call.
   */
  bool notifyChild(PatTermInfo& pi, TNode child, TNode val);
  /**
   * Notify quantified formula
   */
  void notifyQuant(TNode q, TNode p, TNode val);
  /** Quantifiers state */
  QuantifiersState& d_qstate;
  /** Term database */
  TermDb* d_tdb;
  /** Map quantified formulas to their info */
  std::map<Node, QuantInfo> d_quantInfo;
  /** Free variable info */
  std::map<Node, FreeVarInfo> d_fvInfo;
  /** Pattern term info */
  std::map<Node, PatTermInfo> d_pInfo;
  /** Equivalence class info */
  std::map<Node, EqcInfo> d_eqcInfo;
  /** Match equivalence class info */
  std::map<Node, MatchEqcInfo> d_meqcInfo;
  /** The sink node */
  Node d_sink;
  /** common constants */
  Node d_true;
  Node d_false;
  // --------------------------- temporary state
  /** Ground equivalence classes. */
  std::unordered_set<TNode> d_groundEqc;
  /** Ground equivalence classes per type */
  std::map<TypeNode, std::unordered_set<TNode>> d_typeGroundEqc;
  /** Empty set */
  std::unordered_set<TNode> d_emptyEqc;
  /** total number of alive quantified formulas */
  context::CDO<size_t> d_numActiveQuant;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
