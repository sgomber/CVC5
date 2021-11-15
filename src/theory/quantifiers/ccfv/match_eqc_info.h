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

namespace cvc5 {
namespace theory {
namespace quantifiers {

  class TermDb;
  
namespace ccfv {

/**
 * For matching
 */
class MatchEqcInfo
{
 public:
  /** the set of match operators in this equivalence class */
  std::unordered_map<TNode, std::vector<TNode> > d_matchOps;
  /** initialize */
  void initialize(TNode rep, eq::EqualityEngine* ee, TermDb* tdb);
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
