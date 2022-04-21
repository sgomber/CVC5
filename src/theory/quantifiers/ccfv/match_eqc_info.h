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
 * Info per equivalence class for matching in CCFV.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__MATCH_EQC_INFO_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__MATCH_EQC_INFO_H

#include <unordered_map>

#include "expr/node.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDb;

namespace ccfv {

class State;

/**
 * For matching, caches a map of matchable terms in an equivalence class.
 */
class MatchEqcInfo
{
 public:
  /**
   * Mapping from match operators to terms in this equivalence over that
   * match operator, whose arguments are normalized to be representatives.
   * Notice that this means that we only consider terms that are unique
   * modulo congruence.
   * For example for E-graph: { c, a }, { g(b), b }
   * f(a,b) ---> f(c,g(b))
   * f(c,b) ---> f(c,g(b))
   * f(a,a) ---> f(c,c)
   *
   * Notice that we use match operators to resolve overloading, e.g.
   * array select terms (select t1 t2) and (select s1 s2) are indexed separately
   * if t1,t2 have different types than s1,s2.
   */
  std::unordered_map<TNode, std::vector<Node> > d_matchOps;
  /** initialize this equivalence class information */
  void initialize(TNode rep,
                  const State& s,
                  eq::EqualityEngine* ee,
                  TermDb* tdb);
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
