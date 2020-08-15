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

void CombinationModelBased::combineTheories()
{
  // TODO
}

}  // namespace theory
}  // namespace CVC4
