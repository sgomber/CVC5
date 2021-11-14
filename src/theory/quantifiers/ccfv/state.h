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

#include "smt/env_obj.h"
#include "theory/quantifiers/ccfv/quant_info.h"
#include "theory/quantifiers/ccfv/free_var_info.h"
#include "theory/quantifiers/ccfv/pattern_term_info.h"
#include "theory/quantifiers/ccfv/eqc_info.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

class CongruenceClosureFv;
  
class State : protected EnvObj
{
  friend class CongruenceClosureFv;
 public:
  State(Env& env);
  /** Get quantifiers info */
  QuantInfo& getOrMkQuantInfo(TNode q);
  const QuantInfo& getQuantInfo(TNode q) const;
  /** Get free variable info */
  FreeVarInfo& getOrMkFreeVarInfo(TNode v);
  const FreeVarInfo& getFreeVarInfo(TNode v) const;
  /** Get pattern term info */
  PatTermInfo& getOrMkPatTermInfo(TNode p);
  const PatTermInfo& getPatTermInfo(TNode p) const;
  /** Get equivalence class info */
  EqcInfo& getOrMkEqcInfo(TNode r);
 private:
  /** The set of quantified formulas */
  QuantifiersSet d_qset;
  /** Map quantified formulas to their info */
  std::map<Node, QuantInfo> d_quantInfo;
  /** Free variable info */
  std::map<Node, FreeVarInfo> d_fvInfo;
  /** Pattern term info */
  std::map<Node, PatTermInfo> d_pInfo;
  /** Equivalence class info */
  std::map<Node, EqcInfo> d_eqcInfo;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
