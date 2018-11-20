/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Martin Brain
 ** Copyright (c) 2009-2015  New York University and The University of Iowa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An enumerator for floating-point numbers.
 **
 ** An enumerator for floating-point numbers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__FP__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__FP__TYPE_ENUMERATOR_H

#include "expr/kind.h"
#include "expr/type_node.h"
#include "theory/type_enumerator.h"
#include "util/bitvector.h"
#include "util/floatingpoint.h"

namespace CVC4 {
namespace theory {
namespace fp {

class FloatingPointEnumerator
    : public TypeEnumeratorBase<FloatingPointEnumerator> {
 public:
  FloatingPointEnumerator(TypeNode type,
                          TypeEnumeratorProperties* tep = nullptr)
      : TypeEnumeratorBase<FloatingPointEnumerator>(type),
        d_e(type.getFloatingPointExponentSize()),
        d_s(type.getFloatingPointSignificandSize()),
        d_state(d_e + d_s, 0U),
        d_enumerationComplete(false),
        d_doSigned(true),
        d_currentNaN(false) {}

  /** Throws NoMoreValuesException if the enumeration is complete. */
  Node operator*() override {
    if (d_enumerationComplete) {
      throw NoMoreValuesException(getType());
    }
    return NodeManager::currentNM()->mkConst(createFP());
  }

  FloatingPointEnumerator& operator++() override {
    if (d_currentNaN) {
      d_enumerationComplete = true;
    } else {
      d_state = d_state + BitVector(d_state.getSize(), 1U);
      const FloatingPoint next(createFP());
      if( next.isNaN() )
      {
        if( d_doSigned )
        {
          d_doSigned = false;
          d_state = BitVector(d_state.getSize(),Integer(2).pow(d_state.getSize()-1));
        }
        else
        {
          d_currentNaN = true;
        }
      }
    }
    return *this;
  }

  bool isFinished() override { return d_enumerationComplete; }

 protected:
  FloatingPoint createFP(void) const {
    // Rotate the LSB into the sign so that NaN is the last value
    const BitVector value =
        d_state.logicalRightShift(1) | d_state.leftShift(d_state.getSize() - 1);

    return FloatingPoint(d_e, d_s, value);
  }

 private:
  const unsigned d_e;
  const unsigned d_s;
  BitVector d_state;
  bool d_enumerationComplete;
  /** do we still need to enumerate the negative values? */
  bool d_doSigned;
  /** does the current state correspond to NaN? */
  bool d_currentNaN;
}; /* FloatingPointEnumerator */

class RoundingModeEnumerator
    : public TypeEnumeratorBase<RoundingModeEnumerator> {
 public:
  RoundingModeEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr)
      : TypeEnumeratorBase<RoundingModeEnumerator>(type),
        d_rm(roundNearestTiesToEven),
        d_enumerationComplete(false) {}

  /** Throws NoMoreValuesException if the enumeration is complete. */
  Node operator*() override {
    if (d_enumerationComplete) {
      throw NoMoreValuesException(getType());
    }
    return NodeManager::currentNM()->mkConst(d_rm);
  }

  RoundingModeEnumerator& operator++() override {
    switch (d_rm) {
      case roundNearestTiesToEven:
        d_rm = roundTowardPositive;
        break;
      case roundTowardPositive:
        d_rm = roundTowardNegative;
        break;
      case roundTowardNegative:
        d_rm = roundTowardZero;
        break;
      case roundTowardZero:
        d_rm = roundNearestTiesToAway;
        break;
      case roundNearestTiesToAway:
        d_enumerationComplete = true;
        break;
      default:
        Unreachable("Unknown rounding mode?");
        break;
    }
    return *this;
  }

  bool isFinished() override { return d_enumerationComplete; }

 private:
  RoundingMode d_rm;
  bool d_enumerationComplete;
}; /* RoundingModeEnumerator */

}  // namespace fp
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__FP__TYPE_ENUMERATOR_H */
