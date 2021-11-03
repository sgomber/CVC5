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
 * Implementation of lambda lifting.
 */

#include "theory/uf/lambda_lift.h"

#include "expr/skolem_manager.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace uf {

LambdaLift::LambdaLift(Env& env)
    : EnvObj(env)
{
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5
