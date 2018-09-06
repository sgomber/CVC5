/*********************                                                        */
/*! \file expand.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief expand
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS___H
#define __CVC4__THEORY__QUANTIFIERS___H

#include <map>
#include "expr/node.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

  
class Expand
{
public:
  Expand();

  static Node expand( Node q );
};
  
/** Expand
 * 
 * This module is used to recognize when a quantified formula should be
 * eagerly expanded. For example, if the constants of type T are a,b,c, then
 * a quantified formula forall x:T. P( x ) is equivalent to P(a) ^ P(b) ^ P(c).
 * We say that P(a) ^ P(b) ^ P(c) is the expanded form of forall x:T. P(x).
 */
class QuantifierExpander : public QuantifiersReducer
{
public:
  QuantifierExpander( QuantifiersEngine * qe );
  ~QuantifierExpander(){}
  /** determine whether this quantified formula will be reduced */
  bool shouldReduce(Node q) override;
  /** do reduction for quantified formula q */
  void doReduce( Node q ) override;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const override { return "QuantDSplit"; }
private:
  /** pointer to quantifiers engine */
  QuantifiersEngine * d_qe;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS___H */
