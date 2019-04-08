/*********************                                                        */
/*! \file subsume.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Subsumption
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SUBSUME_H
#define __CVC4__THEORY__QUANTIFIERS__SUBSUME_H


#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * A quantifiers module that computes reductions based on alpha-equivalence,
 * using the above utilities.
 */
class Subsume
{
 public:
  Subsume(QuantifiersEngine* qe);
  ~Subsume(){}
  /** set subsumes 
   * 
   * This indicates that q subsumes qsubsumed. This call is legal if:
   *   q |= qsubsumed.
   */
  void setSubsumes( Node q, Node qsubsumed );
private:
  /** map quantified formulas to those they subsume */
  std::map<Node, std::vector<Node>> d_subsumes;
  /** map quantified formulas to those they are subsumed by */
  std::map<Node, std::vector<Node>> d_subsumed_by;
};

}
}
}

#endif
