#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SAMPLE__THEORY_SAMPLE_H
#define __CVC4__THEORY__SAMPLE__THEORY_SAMPLE_H

#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace sample {

class TheorySample : public Theory {
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
public:

  /** Constructs a new instance of TheorySample w.r.t. the provided contexts. */
  TheorySample(context::Context* c,
               context::UserContext* u,
               OutputChannel& out,
               Valuation valuation,
               const LogicInfo& logicInfo);

  void check(Effort) override;

  std::string identify() const override {
    return "THEORY_SAMPLE";
  }
  /** needs check last effort */
  bool needsCheckLastEffort() override;
  /** finish init */
  void finishInit() override;
private:
  /** common nodes */
  Rational d_rmax;
  Node d_true;
  
  NodeSet d_not_elim;
  NodeSet d_sample_checks;
  /** number of samples */
  unsigned d_num_samples;
  /** number of samples we allow to be not sat */
  unsigned d_num_samples_nsat;
  /** whether a term is a sampling term */
  std::map< Node, bool > d_isSample;
  /** whether a term has sampling subterms */
  std::map< Node, bool > d_hasSample;
  /** assertion information */
  class AssertInfo 
  {
  public:
    /** free terms */
    std::vector< Node > d_free_terms;
    /** sample terms */
    std::vector< Node > d_sample_terms;
    /** init */
    void init() {}
  };
  std::map< Node, AssertInfo > d_ainfo;
  
  class TypeInfo
  {
  public:
    Node d_value;
    unsigned d_ncons;
    std::vector< bool > d_builtin;
    std::vector< Node > d_ops;
    std::vector< Kind > d_kinds;
    std::vector< std::vector< TypeNode > > d_args;
    /** for random calls */
    std::vector< unsigned > d_rmin;
    std::vector< unsigned > d_rmax;
    /** init */
    void init() {}
  };
  std::map<TypeNode, TypeInfo > d_tinfo;
  
  /** register sample check constraint */
  void registerSampleCheck(Node n);
  
  
  /** register sample term */
  void registerSampleType(TypeNode tn);

  /** check last call */
  void checkLastCall();
  /** check */
  bool runCheck();
  /** the master equality engine (used for explainations */
  eq::EqualityEngine * d_masterEe;
  /** explain model value */
  Node explainModelValue(Node n, std::vector< Node >& vec);
  
  //-------------------------per last call effort check
  std::vector< Node > d_asserts;
  std::vector< Node > d_basserts;
  std::map< Node, std::map< unsigned, Node > > d_assert_to_value;
  /** get base model value 
   * 
   * This function returns a term where all non-sampling operators have been
   * replaced by their value in the current model.
   */
  Node getBaseModelValue(Node n);
  /** cache of the above function */
  std::unordered_map< Node, Node, NodeHashFunction > d_bmv;
  /** base sampling terms for this round */
  std::vector< Node > d_base_sample_terms;
  /** conflict */
  std::unordered_set< Node, NodeHashFunction > d_conflict;
  //-------------------------end per last call effort check

  /** get sample value */
  Node getSampleValue(TypeNode tn);
  /** make value */
  Node mkValue(Node op, std::vector<Node>& children );
  /** cache of the sampling */
  std::map< Node, std::vector< Node > > d_bst_to_values;
  
};/* class TheorySample */

}/* CVC4::theory::sample namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SAMPLE__THEORY_SAMPLE_H */
