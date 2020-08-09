/*********************                                                        */
/*! \file combination_distributed.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for theory combination.
 **/

#include "theory/combination_distributed.h"

namespace CVC4 {
namespace theory {


CombinationDistributed::CombinationDistributed(TheoryEngine& te) : d_te(te) {}

CombinationDistributed::~CombinationDistributed()
{
}

void CombinationDistributed::finishInit()
{
}

void CombinationDistributed::combineTheories()
{
}

void CombinationDistributed::resetModel()
{
  d_mDistributed->resetModel();
}

bool CombinationDistributed::buildModel()
{
  return d_mDistributed->buildModel();
}

void CombinationDistributed::postProcessModel(bool incomplete)
{
  d_mDistributed->postProcessModel(incomplete);
}

theory::TheoryModel* CombinationDistributed::getModel()
{
  return d_mDistributed->getModel();
}


}  // namespace theory
}  // namespace CVC4
