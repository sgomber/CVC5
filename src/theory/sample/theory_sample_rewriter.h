#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SAMPLE__THEORY_SAMPLE_REWRITER_H
#define __CVC4__THEORY__SAMPLE__THEORY_SAMPLE_REWRITER_H

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace sample {

class TheorySampleRewriter
{
 public:
  /** post-rewrite */
  static RewriteResponse postRewrite(TNode node);

  /** pre-rewrite */
  static RewriteResponse preRewrite(TNode node);

  /**
   * Rewrite an equality, in case special handling is required.
   */
  static Node rewriteEquality(TNode equality)
  {
    // often this will suffice
    return postRewrite(equality).node;
  }

  /**
   * Initialize the rewriter.
   */
  static inline void init()
  {
    // nothing to do
  }

  /**
   * Shut down the rewriter.
   */
  static inline void shutdown()
  {
    // nothing to do
  }
  /** is sample type */
  static bool isSampleType(TypeNode tn);
}; /* class TheorySampleRewriter */

}  // namespace sample
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__SAMPLE__THEORY_SAMPLE_REWRITER_H */
