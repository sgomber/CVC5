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

#include "theory/quantifiers/ccfv/pattern_term_info.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

PatTermInfo::PatTermInfo(context::Context* c, size_t numVars) : d_eq(c), d_numUnassignVar(c, numVars) {}

bool isActive() const { return d_eq.isNull(); }

}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
