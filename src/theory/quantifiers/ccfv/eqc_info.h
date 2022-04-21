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
 * Info per equivalence class in CCFV.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__EQC_INFO_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__EQC_INFO_H

#include <map>

#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ccfv {

/**
 * For each equivalence class, required information.
 *
 * For pattern term equivalence classes, it may be the case that two pattern
 * terms merge. Examples are:
 *
 * P(x, y) and P(x, z), when y = a, z = a
 * P(x, a) and  P(x, b), when a = b
 */
class EqcInfo
{
  typedef context::CDList<Node> NodeList;

 public:
  EqcInfo(context::Context* c) : d_eqPats(c), d_groundEqc(c) {}
  /** List of terms in this equivalence class that are not the representative */
  NodeList d_eqPats;
  /** The original ground equivalence class for this */
  context::CDO<TNode> d_groundEqc;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
