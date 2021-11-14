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

#include "context/cdo.h"
#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

/**
 * A quantified formula is a pattern term whose parent is
 * the quant
 */
class PatTermInfo
{
 public:
  PatTermInfo(context::Context* c);
  /** initialize */
  void initialize(TNode pattern);
  /**
   * is active, false if it has merged to a ground equivalence class, or if
   * its variables have been fully assigned.
   */
  bool isActive() const;
  /** Notify that child was assigned value val, set eq if possible. */
  bool notify(TNode child, TNode val, bool isSink);
  /** 
   * This pattern term.
   */
  Node d_pattern;
  /** the ground term we are equal to, if any */
  context::CDO<TNode> d_eq;
  /** The number of unassigned children */
  context::CDO<size_t> d_numUnassignChildren;

  /**
   * Map from equivalence classes to pattern terms that require
   * this pattern to be in the equivalence class of that term. If the pattern
   * term merges into a equivalence class that is not that equivalence class,
   * the quantified formula has no propagating substitution in the context, and
   * hence it is marked dead.
   */
  //std::map<TNode, std::vector<TNode> > d_gEqReq;
  /** Same as above, for disequality requirements */
  //std::map<TNode, std::vector<TNode> > d_gDeqReq;

  /**
   * The list of pattern terms that are the parent of this. For pattern p,
   * this is either:
   * (1) A term of the form f( ... p ... ), where f may be a Boolean connective.
   * (2) A quantified formula Q whose body has p as a disjunct.
   */
  std::vector<TNode> d_parentNotify;
   /** is Boolean connective */
   bool d_isBooleanConnective;
};

}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
