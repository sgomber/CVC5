/*********************                                                        */
/*! \file lazy_tpp_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The lazy theory preprocess solver
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP__LAZY_TPP_SOLVER_H
#define CVC4__PROP__LAZY_TPP_SOLVER_H

#include <vector>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "prop/theory_preprocess_solver.h"
#include "theory/trust_node.h"

namespace CVC4 {
namespace prop {

/**
 */
class LazyTppSolver : public TheoryPreprocessSolver
{
  using NodeSet = context::CDHashSet<Node, NodeHashFunction>;

 public:
  LazyTppSolver(PropEngine& propEngine,
                TheoryEngine& theoryEngine,
                context::UserContext* userContext,
                ProofNodeManager* pnm = nullptr);

  ~LazyTppSolver();

  /**
   * Notify this module that assertion is being asserted to the theory engine.
   * This adds the skolems of assertions to the set of active skolems
   * (d_activeSkolems) which we ensure lemmas have been produced for.
   */
  void notifyAssertFact(TNode assertion) override;

  /**
   * Call the preprocessor on node, return LEMMA trust node corresponding to
   * the preprocessed lemma.
   */
  theory::TrustNode preprocessLemma(theory::TrustNode trn,
                                    std::vector<theory::TrustNode>& newLemmas,
                                    std::vector<Node>& newSkolems,
                                    Node& retLemma) override;
  /**
   * Call the preprocessor on node, return REWRITE trust node corresponding to
   * the rewrite.
   */
  theory::TrustNode preprocess(TNode node,
                               std::vector<theory::TrustNode>& newLemmas,
                               std::vector<Node>& newSkolems) override;
  /**
   * Remove term ITEs (and more generally, term formulas) from the given node.
   * Return the REWRITE trust node corresponding to rewriting node. New lemmas
   * and skolems are added to ppLemmas and ppSkolems respectively.
   */
  theory::TrustNode removeItes(TNode node,
                               std::vector<theory::TrustNode>& ppLemmas,
                               std::vector<Node>& ppSkolems) override;

  /** check method */
  void check(theory::Theory::Effort effort) override;
  /** needs check method */
  bool needCheck() override;

 private:
  /**
   * Set of activated skolems, collected during calls to notifyAssertFact
   * and cleared during check.
   */
  std::unordered_set<Node, NodeHashFunction> d_activeSkolems;
  /** Set of skolems whose lemmas have been processed */
  NodeSet d_processedSkolems;
  /** Have we added lemmas on the last call to check? */
  bool d_lemmasAdded;
};

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__LAZY_TPP_SOLVER_H */
