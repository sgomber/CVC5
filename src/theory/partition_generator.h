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
 * PartitionGenerator for creating partitions.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SPLITTER_H
#define CVC5__THEORY__SPLITTER_H

#include <vector>

#include "proof/trust_node.h"
#include "theory/theory.h"
#include "theory/theory_engine_module.h"
#include "expr/plugin.h"

namespace cvc5::internal {


namespace theory {

class PartitionGenerator : public TheoryEngineModule
{
 public:
  PartitionGenerator(Env& env,
                     TheoryEngine* theoryEngine,
                     Plugin& p);

  /**
   * Make partitions for parallel solving. e communicates the effort at which
   * check was called. Returns a lemma blocking off the emitted cube from the
   * search.
   */
  void check(Theory::Effort e) override;

 private:
};
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__PARTITION__GENERATOR_H */
