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

class State;

class FreeVarInfo
{
  typedef context::CDList<Node> NodeList;
  typedef context::CDHashSet<Node> NodeSet;

 public:
  FreeVarInfo(context::Context* c);
  /**
   * Term list, all pattern terms that are fully assigned when we have an
   * assignment for this variable.
   */
  NodeSet d_useList;
  /**
   * List of quantifiers that contain this variable
   */
  NodeList d_quantList;
  /** Add quantifier */
  void addQuantMatch(TNode f, size_t index, TNode q);
  /** Is active? */
  bool isActive() const;
  //--------------------- in search
  /** Reset domain */
  void resetDomain();
  /** Is finished? */
  bool isFinished() const;
  /** Get next argument position to match */
  bool getNextMatchPosition(State* s, TNode& f, size_t& index);

 private:
  /** context */
  context::Context* d_context;
  /** Map from (function, argument position) to quantifiers list */
  std::map<std::pair<TNode, size_t>, NodeList> d_qlist;
  /** Iterator through the above list */
  std::map<std::pair<TNode, size_t>, NodeList>::iterator d_itql;
  /** The list of ground equivalence classes we have already considered */
  std::unordered_set<TNode> d_eqcProcessed;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
