/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Dejan Jovanovic, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bitvector theory typing rules.
 */

#include "theory/bv/theory_bv_type_rules.h"

#include <algorithm>

#include "expr/type_node.h"
#include "util/bitvector.h"
#include "util/cardinality.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

bool checkMaybeBitVector(const TypeNode& tn, std::ostream* errOut)
{
  if (tn.isBitVector())
  {
    return true;
  }
  if (tn.getKind() == kind::ABSTRACT_TYPE)
  {
    Kind ak = tn.getAbstractedKind();
    if (ak == kind::ABSTRACT_TYPE || ak == kind::BITVECTOR_TYPE)
    {
      return true;
    }
  }
  if (errOut)
  {
    (*errOut) << "expecting a bit-vector term";
  }
  return false;
}

Cardinality CardinalityComputer::computeCardinality(TypeNode type)
{
  Assert(type.getKind() == kind::BITVECTOR_TYPE);

  uint32_t size = type.getConst<BitVectorSize>();
  if (size == 0)
  {
    return 0;
  }
  return Integer(2).pow(size);
}

TypeNode BitVectorConstantTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorConstantTypeRule::computeType(NodeManager* nodeManager,
                                                TNode n,
                                                bool check,
                                                std::ostream* errOut)
{
  if (check)
  {
    if (n.getConst<BitVector>().getSize() == 0)
    {
      if (errOut)
      {
        (*errOut) << "constant of size 0";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->mkBitVectorType(n.getConst<BitVector>().getSize());
}

TypeNode BitVectorFixedWidthTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorFixedWidthTypeRule::computeType(NodeManager* nodeManager,
                                                  TNode n,
                                                  bool check,
                                                  std::ostream* errOut)
{
  TNode::iterator it = n.begin();
  TypeNode t = (*it).getType(check);
  if (check)
  {
    if (!checkMaybeBitVector(t, errOut))
    {
      return TypeNode::null();
    }
    TNode::iterator it_end = n.end();
    for (++it; it != it_end; ++it)
    {
      if ((*it).getType(check) != t)
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting bit-vector terms of the same width");
        return TypeNode::null();
      }
    }
  }
  return t;
}

TypeNode BitVectorPredicateTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorPredicateTypeRule::computeType(NodeManager* nodeManager,
                                                 TNode n,
                                                 bool check,
                                                 std::ostream* errOut)
{
  if (check)
  {
    TypeNode lhsType = n[0].getType(check);
    if (!checkMaybeBitVector(lhsType, errOut))
    {
      return TypeNode::null();
    }
    TypeNode rhsType = n[1].getType(check);
    if (lhsType != rhsType)
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting bit-vector terms of the same width");
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

TypeNode BitVectorRedTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorRedTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  if (check)
  {
    TypeNode type = n[0].getType(check);
    if (!checkMaybeBitVector(type, errOut))
    {
      return TypeNode::null();
    }
  }
  return nodeManager->mkBitVectorType(1);
}

TypeNode BitVectorBVPredTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->mkBitVectorType(1);
}
TypeNode BitVectorBVPredTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check,
                                              std::ostream* errOut)
{
  if (check)
  {
    TypeNode lhs = n[0].getType(check);
    TypeNode rhs = n[1].getType(check);
    if (!checkMaybeBitVector(lhs, errOut) || lhs != rhs)
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting bit-vector terms of the same width");
      return TypeNode::null();
    }
  }
  return nodeManager->mkBitVectorType(1);
}

TypeNode BitVectorConcatTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorConcatTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check,
                                              std::ostream* errOut)
{
  uint32_t size = 0;
  for (const auto& child : n)
  {
    TypeNode t = child.getType(check);
    // NOTE: We're throwing a type-checking exception here even
    // when check is false, bc if we don't check that the arguments
    // are bit-vectors the result type will be inaccurate
    if (!checkMaybeBitVector(t, errOut))
    {
      return TypeNode::null();
    }
    size += t.getBitVectorSize();
  }
  return nodeManager->mkBitVectorType(size);
}

TypeNode BitVectorToBVTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->mkBitVectorType(n.getNumChildren());
}

TypeNode BitVectorToBVTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  for (const auto& child : n)
  {
    TypeNode t = child.getType(check);
    if (!t.isBoolean())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting Boolean terms");
    }
  }
  return nodeManager->mkBitVectorType(n.getNumChildren());
}

TypeNode BitVectorITETypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorITETypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  Assert(n.getNumChildren() == 3);
  TypeNode thenpart = n[1].getType(check);
  if (check)
  {
    TypeNode cond = n[0].getType(check);
    if (cond != nodeManager->mkBitVectorType(1))
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting condition to be bit-vector term size 1");
      return TypeNode::null();
    }
    TypeNode elsepart = n[2].getType(check);
    if (thenpart != elsepart)
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting then and else parts to have same type");
      return TypeNode::null();
    }
  }
  return thenpart;
}

TypeNode BitVectorBitOfTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorBitOfTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check,
                                             std::ostream* errOut)
{
  if (check)
  {
    BitVectorBitOf info = n.getOperator().getConst<BitVectorBitOf>();
    TypeNode t = n[0].getType(check);

    if (!checkMaybeBitVector(t, errOut))
    {
      return TypeNode::null();
    }
    if (info.d_bitIndex >= t.getBitVectorSize())
    {
      throw TypeCheckingExceptionPrivate(
          n, "extract index is larger than the bitvector size");
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

TypeNode BitVectorExtractTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorExtractTypeRule::computeType(NodeManager* nodeManager,
                                               TNode n,
                                               bool check,
                                               std::ostream* errOut)
{
  BitVectorExtract extractInfo = n.getOperator().getConst<BitVectorExtract>();

  // NOTE: We're throwing a type-checking exception here even
  // if check is false, bc if we allow high < low the resulting
  // type will be illegal
  if (extractInfo.d_high < extractInfo.d_low)
  {
    throw TypeCheckingExceptionPrivate(
        n, "high extract index is smaller than the low extract index");
    return TypeNode::null();
  }

  if (check)
  {
    TypeNode t = n[0].getType(check);
    if (!checkMaybeBitVector(t, errOut))
    {
      return TypeNode::null();
    }
    if (extractInfo.d_high >= t.getBitVectorSize())
    {
      throw TypeCheckingExceptionPrivate(
          n, "high extract index is bigger than the size of the bit-vector");
      return TypeNode::null();
    }
  }
  return nodeManager->mkBitVectorType(extractInfo.d_high - extractInfo.d_low
                                      + 1);
}

TypeNode BitVectorRepeatTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorRepeatTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check,
                                              std::ostream* errOut)
{
  TypeNode t = n[0].getType(check);
  // NOTE: We're throwing a type-checking exception here even
  // when check is false, bc if the argument isn't a bit-vector
  // the result type will be inaccurate
  if (!checkMaybeBitVector(t, errOut))
  {
    return TypeNode::null();
  }
  uint32_t repeatAmount = n.getOperator().getConst<BitVectorRepeat>();
  if (repeatAmount == 0)
  {
    throw TypeCheckingExceptionPrivate(n, "expecting number of repeats > 0");
    return TypeNode::null();
  }
  return nodeManager->mkBitVectorType(repeatAmount * t.getBitVectorSize());
}

TypeNode BitVectorExtendTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorExtendTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check,
                                              std::ostream* errOut)
{
  TypeNode t = n[0].getType(check);
  // NOTE: We're throwing a type-checking exception here even
  // when check is false, bc if the argument isn't a bit-vector
  // the result type will be inaccurate
  if (!checkMaybeBitVector(t, errOut))
  {
    return TypeNode::null();
  }
  uint32_t extendAmount = n.getKind() == kind::BITVECTOR_SIGN_EXTEND
                              ? n.getOperator().getConst<BitVectorSignExtend>()
                              : n.getOperator().getConst<BitVectorZeroExtend>();
  return nodeManager->mkBitVectorType(extendAmount + t.getBitVectorSize());
}

TypeNode BitVectorEagerAtomTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorEagerAtomTypeRule::computeType(NodeManager* nodeManager,
                                                 TNode n,
                                                 bool check,
                                                 std::ostream* errOut)
{
  if (check)
  {
    TypeNode lhsType = n[0].getType(check);
    if (!lhsType.isBoolean())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting boolean term");
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

TypeNode BitVectorAckermanizationUdivTypeRule::preComputeType(NodeManager* nm,
                                                              TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorAckermanizationUdivTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check, std::ostream* errOut)
{
  TypeNode lhsType = n[0].getType(check);
  if (check)
  {
    if (!lhsType.isBitVector())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
      return TypeNode::null();
    }
  }
  return lhsType;
}

TypeNode BitVectorAckermanizationUremTypeRule::preComputeType(NodeManager* nm,
                                                              TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorAckermanizationUremTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check, std::ostream* errOut)
{
  TypeNode lhsType = n[0].getType(check);
  if (check)
  {
    if (!lhsType.isBitVector())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
      return TypeNode::null();
    }
  }
  return lhsType;
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
