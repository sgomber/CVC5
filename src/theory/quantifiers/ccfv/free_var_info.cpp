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

#include "theory/quantifiers/ccfv/free_var_info.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

FreeVarInfo::FreeVarInfo(context::Context * c) : d_useList(c), d_quantList(c) {}

void FreeVarInfo::resetDomain()
{
  d_eqcDomain.clear();
  d_eqcIndex = 0;
  d_fullyAssignedPat.clear();
}


}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
