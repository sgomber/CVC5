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

#include "theory/strings/strings_mnf.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

StringsMnf::StringsMnf(Env& env,
            SolverState& s,
            InferenceManager& im,
            TermRegistry& tr,
            BaseSolver& bs) : EnvObj(env),
      d_state(s),
      d_im(im),
      d_termReg(tr),
      d_bsolver(bs)
{
}

bool StringsMnf::findModelNormalForms(const std::vector<Node>& stringsEqc)
{
  return false;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

