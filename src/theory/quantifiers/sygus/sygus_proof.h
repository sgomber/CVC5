/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sygus abduction utility, which transforms an arbitrary input into an
 * abduction problem.
 */

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_PROOF_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_PROOF_H

#include <string>
#include <vector>
#include "smt/env_obj.h"
#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {
  
class SolverEngine;

namespace theory {
namespace quantifiers {

/** 
 */
class SygusProof : protected EnvObj
{
 public:
  SygusProof(Env& env);
  /**
   */
  void enumerateProofs(const std::string& name,
                       const std::vector<Node>& asserts);
private:
  /** Get grammar */
  TypeNode getGrammar(const std::vector<Node>& asserts);
  /** The subsolver to initialize */
  std::unique_ptr<SolverEngine> d_subSolver;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS_PROOF_H */
