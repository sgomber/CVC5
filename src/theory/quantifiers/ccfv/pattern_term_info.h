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
 * Info per pattern term in CCFV.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__PATTERN_TERM_INFO_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__PATTERN_TERM_INFO_H

#include <map>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

class TermDb;

namespace ccfv {

/**
 * A quantified formula is a pattern term whose parent is
 * the quant
 */
class PatTermInfo
{
  using NodeList = context::CDList<Node>;
  using NodeSet = context::CDHashSet<Node>;

 public:
  PatTermInfo(context::Context* c);
  /** initialize */
  void initialize(TNode pattern, TermDb* tdb);
  /** Reset round */
  void resetRound();
  /**
   * is active, false if it has merged to a ground equivalence class, or if
   * its variables have been fully assigned.
   */
  bool isActive() const;
  /** Notify that child was assigned value val, set eq if possible. */
  bool notify(TNode child, TNode val, bool isSink);
  /** This pattern term. */
  TNode d_pattern;
  /** The match operator */
  TNode d_matchOp;
  /** is Boolean connective */
  bool d_isBooleanConnective;
  //---------------------- during search
  /**
   * The ground term we are currently equal to, if any. This may also be
   * the sink node.
   */
  context::CDO<TNode> d_eq;
  /**
   * The number of unassigned free variables if a congruence term,
   * or the number of unassigned children otherwise.
   */
  context::CDO<size_t> d_numUnassigned;
  /**
   * The list of pattern terms that are the parent of this. For pattern p,
   * this is either:
   * (1) A term of the form f( ... p ... ), where f may be a Boolean connective.
   * (2) A quantified formula Q whose body has p as a disjunct.
   */
  NodeList d_parentNotify;
  /**
   * The list of pattern terms f( ... p ... ) where we are doing congruence
   * over f. We notify these parents of our value only if become equal to sink.
   */
  NodeList d_parentCongNotify;
  //---------------------- matching
  /** Add watched equivalence class */
  void addWatchEqc(TNode eqc);
  /** Get next watch eqc */
  TNode getNextWatchEqc();
  /** Add maybe equal */
  void addMaybeEqc(TNode eqc);
  /** Is maybe equal? */
  bool isMaybeEqc(TNode eqc) const;

 private:
  //---------------------- matching
  /**
   * Watched equivalence classes. This is the set of equivalence classes that
   * may be relevant if this pattern is equal.
   */
  NodeSet d_watchEqc;
  /** List we are procesing */
  NodeList d_watchEqcList;
  /**
   * Watched equivalence classes we have processed.
   * - If pattern is variable, this is the index we have tried
   * - Otherwise, this is the index in the
   */
  context::CDO<size_t> d_watchEqcIndex;
  /**
   * Maybe equal to set 
   */
  NodeSet d_maybeEqc;
  
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
