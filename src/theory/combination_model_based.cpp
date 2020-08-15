/*********************                                                        */
/*! \file combination_model_based.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a care graph based approach for theory combination.
 **/

#include "theory/combination_model_based.h"

#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

CombinationModelBased::CombinationModelBased(
    TheoryEngine& te, const std::vector<Theory*>& paraTheories)
    : CombinationEngine(te, paraTheories)
{
}

CombinationModelBased::~CombinationModelBased() {}

bool CombinationModelBased::buildModel()
{
  // model was already built in combine theories
  Assert(d_mmUse->isModelBuilt());
  return d_mmUse->buildModel();
}

void CombinationModelBased::combineTheories()
{
  // TODO: change the notification class of the ee if central?
  // TODO
  
  // TODO: change the notification class of the ee back if central?
}

}  // namespace theory
}  // namespace CVC4
