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
 ** \brief Arithmetic theory state.
 **/

#include "theory/arith/arith_infer_manager.h"

#include "theory/arith/equality_solver.h"
#include "theory/arith/theory_arith_private.h"


ArithInferManager::ArithInferManager(Theory& t, TheoryArithPrivate& p, EqualitySolver * es) : InferManager(t), d_private(p), d_esolver(es), d_propagationMap(d_state.getSatContext())
{
  
}

TrustNode ArithInferManager::explainLit(TNode lit)
{
  bool useEqualitySolver = false;
  if (d_eqSolver!=nullptr)
  {
    NodeMap::const_iterator it = d_propagationMap.find(lit);
    Assert (it!=d_propagationMap.end());
    if ((*it).second)
    {
      // explain using the equality solver
      return d_esolver->explainLit(lit);
    }
  }
  // otherwise we explain with the private solver
  Node exp = d_private->explain(lit);
  return TrustNode::mkTrustPropExp(lit, exp, nullptr);
}

bool ArithInferManager::propagateManagedLit(TNode lit, bool fromPrivate)
{
  if (d_eqSolver!=nullptr)
  {
    d_propagationMap[lit] = fromPrivate;
  }
  return propagateLit(lit);
}


}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
