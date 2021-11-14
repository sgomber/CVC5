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

#include "context/cdhashset.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/ccfv/eqc_info.h"
#include "theory/quantifiers/ccfv/free_var_info.h"
#include "theory/quantifiers/ccfv/pattern_term_info.h"
#include "theory/quantifiers/ccfv/quant_info.h"

namespace cvc5 {

namespace expr {
class TermCanonize;
}

namespace theory {
namespace quantifiers {

class QuantifiersState;

namespace ccfv {

class CongruenceClosureFv;

class State : protected EnvObj
{
  typedef context::CDHashSet<Node> NodeSet;
  friend class CongruenceClosureFv;

 public:
  State(Env& env, QuantifiersState& qs);
  /** Is finished */
  bool isFinished() const;
  /** Activate quantified formula */
  // void activateQuant(TNode q);

  /** Get quantifiers info */
  QuantInfo& getOrMkQuantInfo(TNode q, expr::TermCanonize& tc);
  QuantInfo& getQuantInfo(TNode q);
  /** Get free variable info */
  FreeVarInfo& getOrMkFreeVarInfo(TNode v);
  const FreeVarInfo& getFreeVarInfo(TNode v) const;
  /** Get pattern term info */
  PatTermInfo& getOrMkPatTermInfo(TNode p);
  PatTermInfo& getPatTermInfo(TNode p);
  /** Get equivalence class info */
  EqcInfo& getOrMkEqcInfo(TNode r);

  /**
   * Called when it is determined what pattern p is equal to.
   *
   * If g is non-null, then g is the (ground) equivalence class that pattern p
   * is equal to. If g is null, then we have determined that p will *never*
   * merge into a ground equivalence class in this context.
   */
  void notifyPatternEqGround(TNode p, TNode g);

  /** Get sink node */
  Node getSink() const;
  /** Is sink */
  bool isSink(TNode n) const;
  /** Get value */
  TNode getValue(TNode p) const;

 private:
  /**
   * Notify that child was assigned value val, set eq if possible.
   * Return true if we set eq during this call.
   */
  bool notify(PatTermInfo& pi, TNode child, TNode val);
  /**
   * Notify quantified formula
   */
  void notifyQuant(TNode q, TNode p, TNode val);
  /** Quantifiers state */
  QuantifiersState& d_qstate;
  /** Map quantified formulas to their info */
  std::map<Node, QuantInfo> d_quantInfo;
  /** Free variable info */
  std::map<Node, FreeVarInfo> d_fvInfo;
  /** Pattern term info */
  std::map<Node, PatTermInfo> d_pInfo;
  /** Equivalence class info */
  std::map<Node, EqcInfo> d_eqcInfo;
  /** The sink node */
  Node d_sink;
  /** the set of ground equivalence classes */
  NodeSet d_groundEqc;
  /** total number of alive quantified formulas */
  context::CDO<size_t> d_numActiveQuant;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
