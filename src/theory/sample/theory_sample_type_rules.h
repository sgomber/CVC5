#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SAMPLE__THEORY_SAMPLE_TYPE_RULES_H
#define __CVC4__THEORY__SAMPLE__THEORY_SAMPLE_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace sample {

class SampleTypeRule {
public:

  /**
   * Compute the type for (and optionally typecheck) a term belonging
   * to the theory of sample.
   *
   * @param check if true, the node's type should be checked as well
   * as computed.
   */
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check)
    throw (TypeCheckingExceptionPrivate) {

    // TODO: implement me!
    Unimplemented();

  }

};/* class SampleTypeRule */

}/* CVC4::theory::sample namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SAMPLE__THEORY_SAMPLE_TYPE_RULES_H */
