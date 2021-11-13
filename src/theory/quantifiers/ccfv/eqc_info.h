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

#include "expr/node.h"
#include "context/cdlist.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

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
  EqcInfo(context::Context * c);
  /** List of terms in this equivalence class that are not the representative */
  NodeList d_eqPats;
};


}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
