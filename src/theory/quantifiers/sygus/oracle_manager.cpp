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
 * Oracle manager for synthesis modulo oracles
 */

#include "theory/quantifiers/sygus/oracle_manager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

OracleManager::OracleManager(OracleChecker& oc) : d_oc(oc) {}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
