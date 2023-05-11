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
  TheoryEngine* d_engine;
  Node d_true;
  bool d_doGeneralize;
  bool d_generalizeMaj;

  bool decomposeLemma(const Node& lem,
                      Subs& s,
                      std::map<Node, Node>& varToExp,
                      std::vector<TNode>& tgtLits) const;
  bool checkSubstitution(const Subs& s, const Node& tgtLit) const;
  /**
   * Called when checkSubstitution { v -> s }, tgtLit returns true.
   * Returns true if any assignment s' for v in a is also such that
   * checkSubstitution { v -> s' } tgtLit returns true.
   */
  Node checkGeneralizes(Assigner* a,
                        const Node& v,
                        const Node& s,
                        const Node& tgtLit);
  /**
   * Cache of checkGeneralizes, storing (a->getSatLiteral, v, tgtLit)
   */
  std::map<std::tuple<Node, Node, Node>, Node> d_genCache;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__ASSIGNER_H */
