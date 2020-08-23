/*********************                                                        */
/*! \file combination_model_based.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a care graph based approach for theory combination.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__COMBINATION_MODEL_BASED__H
#define CVC4__THEORY__COMBINATION_MODEL_BASED__H

#include <map>
#include <memory>

#include "theory/combination_engine.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Manager for doing theory combination using a model-based approach. This is
 * typically done via a central equalty engine architecture.
 */
class CombinationModelBased : public CombinationEngine
{
 public:
  CombinationModelBased(TheoryEngine& te,
                        const std::vector<Theory*>& paraTheories);
  ~CombinationModelBased();

  /** Build model (a no-op) */
  bool buildModel() override;
  /**
   * Combine theories using model building.
   */
  void combineTheories() override;

 private:
  /** 
   * Model-based notification class, which catches conflicts that arise during
   * model building.
   */
  class ModelBasedNotifyClass : public theory::eq::EqualityEngineNotify {
  public:
    ModelBasedNotifyClass(CombinationModelBased& cmb): d_cmb(cmb) {}
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override
    {
      return true;
    }

    bool eqNotifyTriggerTermEquality(theory::TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override
    {
      return true;
    }

    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override
    {
      //d_cmb.notifyModelConstantTermMerge(t1, t2);
    }

    void eqNotifyNewClass(TNode t) override {}
    void eqNotifyMerge(TNode t1, TNode t2) override {
      //d_cmb.notifyModelMerge(t1, t2);
    }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override {}
  private:
    /** The parent class, which processes the conflict */
    CombinationModelBased& d_cmb;
  };
   
  /**
   * Run the combination framework, model-based version.
   *
   * This first calls TheoryEngineModelBuilder::buildModel. This may either lead
   * to the equality engine of the model becoming inconsistent during the
   * building process, or otherwise succeed.
   *
   * (A) In the case the equality engine is consistent, we have two subcases:
   *
   * (A1) For operators f belonging to parametric theories, if there exists a
   * pair of f-applications such that:
   *   f(t1, ..., tn )^M != f( s1, ..., sn )^M, t1^M=s1^M, ..., tn^M=sn^M
   * then we split on a subset of the equalities of the form ti == si above.
   *
   * (A2) If all pairs of congruent terms are equal in the model, we are done.
   *
   * (B) In the case the equality engine is inconsistent, we check all
   * equivalence classes that contain two shared terms t and s. If two theories
   * disagree on the status of the equality t == s, we split on t == s.
   */
  void combineTheoriesOld();

  void eqNotifyNewClass(TNode node);
  void eqNotifyMerge(TNode t1, TNode t2);
  //-----------------------------------model-based theory combination
  /** check pair
   *
   * Check the status of the equality a == b based on theory tid, where
   * tparametric stores if the theory of tid is parametric. This updates
   * the d_sharedEq and d_sharedDeq mappings below.
   */
  unsigned checkPair(TNode a, TNode b, theory::TheoryId tid, bool tparametric);
  /** check shared term maps
   *
   * This calls checkSplitCandidate( a, b, T1, T2 ) for all a and b such that
   * d_sharedEq[a][b] and d_sharedDeq[a][b] are both mapped to ids, T1 and T2.
   */
  unsigned checkSharedTermMaps(
      const std::map<theory::TheoryId,
                     std::unordered_set<TNode, TNodeHashFunction> >& tshared);
  /** check split candidate
   *
   * Checks whether the equality a == b should be split on based on the cache
   * and whether or not the theories t1 and t2 are parametric. This is called
   * under two conditions:
   *
   * (1) There exists a pair of congruent disequal terms in the model, i.e.:
   *     f(t1, ..., tn )^M != f( s1, ..., sn )^M, t1^M=s1^M, ..., tn^M=sn^M.
   *     For alll ti, if T1 = theoryOf( f ) != theoryOf( ti.getType() ) = T2,
   *     we call this method on ( ti, si, T1, T2 ).
   * (2) If t and s are shared terms of T1 and T2, t^M = s^M and T1 and T2 (may)
   *     disagree on the status of t==s, we call this method on
   *     ( t, s, T1, T2 ).
   */
  unsigned checkSplitCandidate(TNode a,
                               TNode b,
                               theory::TheoryId t1,
                               theory::TheoryId t2);
  /** merge shared term equivalence classes */
  void mergeSharedTermEqcs(TNode t1, TNode t2);
  //-----------------------------------end model-based theory combination

  //-------------------------caches per model-based theory combination call
  /** cached of equalities we have split on */
  std::unordered_set<Node, NodeHashFunction> d_split_eq_rew;
  /** cached of terms we have split on */
  std::unordered_set<Node, NodeHashFunction> d_split_terms;
  /** for each node pair, a theory whose equality status is (possibly) true */
  std::unordered_map<
      TNode,
      std::unordered_map<TNode, theory::TheoryId, TNodeHashFunction>,
      TNodeHashFunction>
      d_sharedEq;
  /** for each node pair, a theory whose equality status is (possibly) false */
  std::unordered_map<
      TNode,
      std::unordered_map<TNode, theory::TheoryId, TNodeHashFunction>,
      TNodeHashFunction>
      d_sharedDeq;
  //-------------------------end caches per model-based theory combination call

  /** shared terms merge map
   *
   * This is a map from equivalence class representatives in the model's
   * equality engine to shared terms that it contains. It is reset on every
   * new call to building the model.
   */
  std::map<TNode, std::vector<TNode> > d_shared_terms_merge;
  /** */
  SharedTermsDatabase* d_sharedTerms;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__COMBINATION_MODEL_BASED__H */
