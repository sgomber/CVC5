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
private:
  NodeSet d_not_elim;
  NodeSet d_sample_checks;
  /** check last call */
  void checkLastCall();
  /** get model value */
  //Node getModelValue(
};/* class TheorySample */

}/* CVC4::theory::sample namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SAMPLE__THEORY_SAMPLE_H */
