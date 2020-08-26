/*********************                                                        */
/*! \file arith_infer_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arithmetic inference manager
 **/

#include "theory/arith/arith_infer_manager.h"

#include "theory/arith/equality_solver.h"
#include "theory/arith/theory_arith_private.h"

namespace CVC4 {
namespace theory {
namespace arith {

ArithInferManager::ArithInferManager(Theory& t,
                                     TheoryState& state,
                                     TheoryArithPrivate& p)
    : InferManager(t, state),
      d_private(p),
      d_esolver(nullptr),
      d_propagationMap(state.getSatContext())
{
}

void ArithInferManager::setEqualitySolver(EqualitySolver* es)
{
  d_esolver = es;
}

TrustNode ArithInferManager::explainLit(TNode lit)
{
  // if the equality solver exists, we need to see if it was the source of the
  // propagation.
  if (d_esolver != nullptr)
  {
    NodeMap::const_iterator it = d_propagationMap.find(lit);
    // Assert(it != d_propagationMap.end());
    // HACK-centralEe
    // if its not in propagation map, we did it directly in ee central
    if (it == d_propagationMap.end() || !(*it).second)
    {
      // explain using the equality solver
      return d_esolver->explainLit(lit);
    }
  }
  // otherwise we explain with the private solver
  Node exp = d_private.explain(lit);
  return TrustNode::mkTrustPropExp(lit, exp, nullptr);
}

bool ArithInferManager::propagateManagedLit(TNode lit, bool fromPrivate)
{
  if (d_esolver != nullptr)
  {
    if (d_propagationMap.find(lit) != d_propagationMap.end())
    {
      // it's already been propagated (probably by the other module)
      return d_state.isInConflict();
    }
    d_propagationMap[lit] = fromPrivate;
  }
  return propagateLit(lit);
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
