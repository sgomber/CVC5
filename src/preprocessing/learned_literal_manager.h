/*********************                                                        */
/*! \file learned_literal_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   AAndrew Reynolds
 ** This file is part of the CVC5 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The learned literal manager
 **/

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__LEARNED_LITERAL_MANAGER_H
#define CVC5__PREPROCESSING__LEARNED_LITERAL_MANAGER_H

#include "context/cdhashset.h"
#include "expr/node.h"
#include "theory/trust_substitutions.h"

namespace cvc5 {
namespace preprocessing {

class PreprocessingPassContext;

class LearnedLiteralManager
{
 public:
  LearnedLiteralManager(theory::TrustSubstitutionMap& tls,
                        context::UserContext* u,
                        ProofNodeManager* pnm);
  /**
   * Process learned literal. This method is called when a literal is
   * entailed by the current set of assertions.
   *
   * It should be rewritten, and such that top level substitutions have
   * been applied to it.
   */
  void notifyLearnedLiteral(Node lit);
  /** Get learned literals */
  std::vector<Node> getLearnedLiterals();

 private:
  /** Learned literal map */
  typedef context::CDHashSet<Node> NodeSet;
  /* The top level substitutions */
  theory::TrustSubstitutionMap& d_topLevelSubs;
  /** Learned literals */
  NodeSet d_learnedLits;
};

}  // namespace preprocessing
}  // namespace cvc5

#endif /* CVC5__PREPROCESSING__LEARNED_LITERAL_MANAGER_H */
