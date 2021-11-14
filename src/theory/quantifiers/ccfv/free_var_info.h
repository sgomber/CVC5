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

#include <map>

#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

class FreeVarInfo
{
 public:
  /** term list, all pattern terms that contain this variable */
  std::vector<TNode> d_useList;

  /** The list of ground equivalence classes we are considering */
  std::vector<TNode> d_eqcDomain;
  /** The current index in the domain we are searching */
  size_t d_eqcIndex;
  /** The list of terms that have become fully assigned after we assign this */
  std::vector<TNode> d_fullyAssignedPat;

  void resetDomain()
  {
    d_eqcDomain.clear();
    d_eqcIndex = 0;
    d_fullyAssignedPat.clear();
  }
};

}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
