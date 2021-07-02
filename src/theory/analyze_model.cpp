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

std::string printPolarity(bool value, bool valueKnown)
{
  return valueKnown ? ( value ? "" : "~") : "?";
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
  std::stringstream ssa;
  ssa << "(assign"; 
  for (const Node& l : lits)
  {
    size_t id = getOrAssignIdFor(l);
    lvec.push_back(l);
    ids.push_back(id);
    bool value = false;
    bool valueKnown = d_val.hasSatValue(l, value);
    expectedVals.push_back(value);
    expectedValKnown.push_back(valueKnown);
    Assert (valueKnown);
    std::stringstream ssl;
    ssl << " " << printPolarity(value, valueKnown) << id; 
    // is it entailed top-level?
    if (d_entailed.find(id)!=d_entailed.end())
    {
      continue;
    }
    if (d_val.getDecisionLevel(l) == 0 && d_val.getIntroLevel(l) == 0)
    {
      Trace("analyze-model") << "(entailed" << ssl.str() << ")" << std::endl;
      Trace("analyze-model-debug") << "(entailed-debug" << " " << l << ")" << std::endl;
      d_entailed.insert(id);
      continue;
    }
    ssa << ssl.str(); 
  }
  Trace("analyze-model") << ssa.str() << ")" << std::endl;
  
  // compute subset that is false in model
  std::vector<size_t> falseIds;
  Trace("analyze-model") << "(assign-false";
  std::stringstream ssd;
  ssd << "(assign-false-debug";
  for (size_t i=0, nlits = lvec.size(); i<nlits; i++)
  {
    Node litv = d_model->getValue(lvec[i]);
    if (litv.isConst() && litv.getConst<bool>()==expectedVals[i])
    {
      continue;
    }
    falseIds.push_back(ids[i]);
    Trace("analyze-model") << " " << printPolarity(expectedVals[i], expectedValKnown[i]) << ids[i];
    ssd << " " << printPolarity(expectedVals[i], expectedValKnown[i]) << lvec[i];
  }
  Trace("analyze-model") << ")" << std::endl;
  Trace("analyze-model-debug") << ssd.str() << ")" << std::endl;
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
