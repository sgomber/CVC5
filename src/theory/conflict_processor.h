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

#include "cvc5_public.h"

#ifndef CVC5__THEORY__CONFLICT_PROCESSOR_H
#define CVC5__THEORY__CONFLICT_PROCESSOR_H

#include "expr/node.h"
#include "expr/subs.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

class TheoryEngine;
class Assigner;

namespace theory {

class ConflictProcessor : protected EnvObj
{
 public:
  ConflictProcessor(Env& env, TheoryEngine* te);
  ~ConflictProcessor() {}

  TrustNode processLemma(const TrustNode& lem);

 private:
  /** The parent engine */
  TheoryEngine* d_engine;
  Node d_true;
  bool d_doGeneralize;
  /** Statistics about the conflict processor */
  struct Statistics
  {
    Statistics(StatisticsRegistry& sr);
    /** Total number of lemmas */
    IntStat d_lemmas;
    /** Total number of minimized lemmas */
    IntStat d_minLemmas;
    /** Total number of generalized lemmas */
    IntStat d_genLemmas;
  };
  Statistics d_stats;
  void decomposeLemma(const Node& lem,
                      Subs& s,
                      std::map<Node, Node>& varToExp,
                      std::vector<TNode>& tgtLits) const;
  bool hasAssigner(const Node& lit) const;
  bool checkSubstitution(const Subs& s, const Node& tgtLit) const;
  bool checkTgtGeneralizes(Assigner* a,
                           Node& tgtLit,
                           Node& tgtLitFinal,
                           const Subs& s,
                           bool& isConflict);
  /**
   * Called when checkSubstitution { v -> s }, tgtLit returns true.
   * Returns a node that also implies tgtLit that is weaker than (= v s).
   *
   * if any assignment s' for v in a is also such that
   * checkSubstitution { v -> s' } tgtLit returns true.
   */
  Node checkSubsGeneralizes(Assigner* a,
                            const Node& v,
                            const Node& s,
                            const Node& tgtLit,
                            bool& isConflict);
  /**
   * Cache of checkGeneralizes, storing (a->getSatLiteral, v, tgtLit)
   */
  std::map<std::tuple<Node, Node, Node>, Node> d_genCache;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__ASSIGNER_H */
