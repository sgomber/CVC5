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


AnalyzeModel::AnalyzeModel(Valuation val, RelevanceManager * rm, TheoryModel * tm) : d_val(val), d_rm(rm), d_model(tm){
  Assert (d_rm!=nullptr);
  
}

void AnalyzeModel::analyzeModelFailure()
{
  bool rsuccess = false;
  const std::unordered_set<TNode>& lits = d_rm->getRelevantAssertions(rsuccess);
  if (!rsuccess)
  {
    Trace("analyze-model") << "AnalyzeModel::analyzeModelFailure: failed to get relevant assertions" << std::endl;
  }
  // assign identifiers to literals for printing
  std::vector<Node> lvec;
  std::vector<size_t> ids;
  std::vector<bool> expectedVals;
  std::vector<bool> expectedValKnown;
  Trace("analyze-model") << "(assign";
  for (const Node& l : lits)
  {
    size_t id = getOrAssignIdFor(l);
    lvec.push_back(l);
    ids.push_back(id);
    Trace("analyze-model") << " " << id;
    bool value = false;
    bool valueKnown = d_val.hasSatValue(l, value);
    expectedVals.push_back(value);
    expectedValKnown.push_back(valueKnown);
  }
  Trace("analyze-model") << ")" << std::endl;
  // compute subset that is false in model
  std::vector<size_t> falseIds;
  Trace("analyze-model") << "(assign-false";
  for (size_t i=0, nlits = lvec.size(); i<nlits; i++)
  {
    Node litv = d_model->getValue(lvec[i]);
    if (litv.isConst() && litv.getConst<bool>()==expectedVals[i])
    {
      continue;
    }
    falseIds.push_back(ids[i]);
    Trace("analyze-model") << " " << ids[i];
  }
  Trace("analyze-model") << ")" << std::endl;
}

size_t AnalyzeModel::getOrAssignIdFor(Node lit)
{
  std::map< Node, size_t >::iterator it = d_litId.find(lit);
  if (it!=d_litId.end())
  {
    return it->second;
  }
  size_t id = d_litId.size();
  Trace("analyze-model") << "(literal " << id << " " << lit << ")" << std::endl;
  d_litId[lit] = id;
  return id;
}

}  // namespace theory
}  // namespace cvc5
