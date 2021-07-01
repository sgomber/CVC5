/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Analyze model utility
 */

#include "theory/analyze_model.h"

#include "theory/theory_model.h"
#include "theory/relevance_manager.h"

namespace cvc5 {
namespace theory {

class TheoryModel;
class RelevanceManager;


AnalyzeModel::AnalyzeModel(Valuation val, RelevanceManager * rm, TheoryModel * tm) : d_val(val), d_rm(rm), d_model(tm){}

void AnalyzeModel::analyzeModelFailure()
{
}

}  // namespace theory
}  // namespace cvc5
