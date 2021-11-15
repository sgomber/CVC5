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
 * Info per free variable in CCFV.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__FREE_VAR_INFO_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__FREE_VAR_INFO_H

#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

class FreeVarInfo
{
  typedef context::CDList<Node> NodeList;
  typedef context::CDHashSet<Node> NodeSet;

 public:
  FreeVarInfo(context::Context* c);
  /** term list, all pattern terms that contain this variable */
  NodeSet d_useList;
  /** quantifiers list */
  NodeList d_quantList;
  //--------------------- in search
  /** The list of ground equivalence classes we have already considered */
  std::unordered_set<TNode> d_eqcProcessed;
  /** The current index in quantifiers */
  size_t d_qindex;
  /** Reset domain */
  void resetRound();
  /** Is finished? */
  bool isFinished() const;
  /** Add quantifier */
  void addQuantMatch(TNode f, size_t index, TNode q);
 private:
  /** context */
  context::Context * d_context;
  /** Map from (function, argument position) to quantifiers list */
  std::map<std::pair<TNode, size_t>, NodeList> d_qlist;
  /** Iterator through the above list */
  std::map<std::pair<TNode, size_t>, NodeList>::iterator d_itql;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
