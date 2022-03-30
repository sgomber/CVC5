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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS__ORACLE_MANAGER_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS__ORACLE_MANAGER_H

#include <unordered_set>

#include "expr/node.h"
#include "theory/quantifiers/oracle_checker.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * To be used for oracle assumptions / constraints.
 */
class OracleManager
{
 public:
  OracleManager(OracleChecker& oc);
  ~OracleManager() {}

 private:
  /** Oracle checker */
  OracleChecker& d_oc;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__ORACLE_MANAGER_H */
