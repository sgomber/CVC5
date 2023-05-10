/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An assigner
 */

#include "theory/conflict_processor.h"

namespace cvc5::internal {
namespace theory {

  ConflictProcessor::ConflictProcessor(Env& env, TheoryEngine* te) : EnvObj(env), d_engine(te) {}
  
  TrustNode ConflictProcessor::processConflict(const TrustNode& conflict)
  {
    return conflict;
  }

}
}  // namespace cvc5::internal

