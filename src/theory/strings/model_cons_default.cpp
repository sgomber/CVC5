/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model normal form finder for strings
 */

#include "theory/strings/model_cons_default.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

ModelConsDefault::ModelConsDefault(Env& env,
                                   SolverState& state,
                                   CoreSolver& csolver)
    : ModelCons(env), d_state(state), d_csolver(csolver)
{
}

void ModelConsDefault::getStringRepresentativesFrom(
    const std::set<Node>& termSet,
    std::unordered_set<TypeNode>& repTypes,
    std::map<TypeNode, std::unordered_set<Node>>& repSet)
{
  d_state.getStringRepresentativesFrom(termSet, repTypes, repSet);
}

void ModelConsDefault::separateByLength(
    const std::vector<Node>& n,
    std::map<TypeNode, std::vector<std::vector<Node>>>& cols,
    std::map<TypeNode, std::vector<Node>>& lts)
{
  d_state.separateByLength(n, cols, lts);
  // TODO: make concrete
}

NormalForm& ModelConsDefault::getNormalForm(Node n)
{
  return d_csolver.getNormalForm(n);
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
