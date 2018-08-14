#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SAMPLE__THEORY_SAMPLE_TYPE_RULES_H
#define __CVC4__THEORY__SAMPLE__THEORY_SAMPLE_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace sample {

class SampleIntUnifTypeRule
{
 public:
  /**
   * Compute the type for (and optionally typecheck) a term belonging
   * to the theory of sample.
   *
   * @param check if true, the node's type should be checked as well
   * as computed.
   */
  inline static TypeNode computeType(
      NodeManager* nodeManager,
      TNode n,
      bool check) throw(TypeCheckingExceptionPrivate)
  {
    Assert(n.getKind() == kind::SAMPLE_INT_UNIF);
    if (check)
    {
      for (unsigned i = 0; i < 2; i++)
      {
        TypeNode tn = n[i].getType(check);
        if (!tn.isInteger())
        {
          throw TypeCheckingExceptionPrivate(
              n, "argument of uniform distribution should be an integer");
        }
      }
    }
    return NodeManager::currentNM()->integerType();
  }

}; /* class SampleCheckOperatorTypeRule */

class SampleRunOperatorTypeRule
{
 public:
  /**
   * Compute the type for (and optionally typecheck) a term belonging
   * to the theory of sample.
   *
   * @param check if true, the node's type should be checked as well
   * as computed.
   */
  inline static TypeNode computeType(
      NodeManager* nodeManager,
      TNode n,
      bool check) throw(TypeCheckingExceptionPrivate)
  {
    Assert(n.getKind() == kind::SAMPLE_RUN);

    TypeNode tn = n[0].getType(check);
    if (!tn.isDatatype())
    {
      throw TypeCheckingExceptionPrivate(
          n, "argument of sample run should be a sample type");
    }
    const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
    if (!dt.isSygus())
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "argument of sample run should be a sample type, but got a datatype");
    }
    return TypeNode::fromType(dt.getSygusType());
  }

}; /* class SampleRunOperatorTypeRule */

class SampleCheckOperatorTypeRule
{
 public:
  /**
   * Compute the type for (and optionally typecheck) a term belonging
   * to the theory of sample.
   *
   * @param check if true, the node's type should be checked as well
   * as computed.
   */
  inline static TypeNode computeType(
      NodeManager* nodeManager,
      TNode n,
      bool check) throw(TypeCheckingExceptionPrivate)
  {
    Assert(n.getKind() == kind::SAMPLE_CHECK);

    TypeNode tn = n[0].getType(check);
    if (!tn.isBoolean())
    {
      throw TypeCheckingExceptionPrivate(
          n, "argument of sample check should be Boolean");
    }
    return tn;
  }

}; /* class SampleCheckOperatorTypeRule */

}  // namespace sample
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__SAMPLE__THEORY_SAMPLE_TYPE_RULES_H */
