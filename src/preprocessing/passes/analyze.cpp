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
 * Analysis of input formula
 */

#include "preprocessing/passes/analyze.h"

#include "expr/skolem_manager.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "util/bitvector.h"

using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace preprocessing {
namespace passes {

Analyze::Analyze(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "analyze")
{
}

PreprocessingPassResult Analyze::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  if (Trace.isOn("analyze"))
  {
    std::unordered_set<TNode> visited;
    std::unordered_set<Kind> kinds;
    size_t size = assertionsToPreprocess->size();
    for (size_t i = 0; i < size; ++i)
    {
      Node n = (*assertionsToPreprocess)[i];
      analyze(n, visited, kinds);
    }
    // analyze constants of each type
    for (const std::pair<const TypeNode, std::vector<Node>>& tc : d_constants)
    {
      analyzeConstants(tc.first, tc.second);
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

void Analyze::analyze(Node n,
                      std::unordered_set<TNode>& visited,
                      std::unordered_set<Kind>& kinds)
{
  std::unordered_set<TNode>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it != visited.end())
    {
      continue;
    }
    visited.insert(cur);
    visit.insert(visit.end(), cur.begin(), cur.end());
    Kind k = cur.getKind();
    TypeNode tn = cur.getType();
    if (cur.isConst())
    {
      d_constants[tn].push_back(cur);
    }
    if (kinds.find(k) == kinds.end())
    {
      kinds.insert(k);
      Trace("analyze") << "Kind: " << k << std::endl;
    }
  } while (!visit.empty());
}

void Analyze::analyzeConstants(TypeNode tn, const std::vector<Node>& cs)
{
  Trace("analyze") << "Constants of type " << tn << ":" << std::endl;
  for (const Node& c : cs)
  {
    if (tn.isBitVector())
    {
      const BitVector& bv = c.getConst<BitVector>();
      Trace("analyze") << "#b" << bv.toString() << std::endl;
    }
    else
    {
      Trace("analyze") << c << std::endl;
    }
  }
  if (tn.isBitVector())
  {
    NodeManager* nm = NodeManager::currentNM();
    std::map<TypeNode, std::unordered_set<Node>> extra_cons;
    for (const Node& c : cs)
    {
      extra_cons[tn].insert(c);
    }
    std::map<TypeNode, std::unordered_set<Node>> exclude_cons;
    std::map<TypeNode, std::unordered_set<Node>> include_cons;
    std::unordered_set<Node> term_irrelevant;
    TypeNode stn =
        quantifiers::CegGrammarConstructor::mkSygusDefaultType(tn,
                                                               Node(),
                                                               "bvc",
                                                               extra_cons,
                                                               exclude_cons,
                                                               include_cons,
                                                               term_irrelevant);
    Node e = nm->getSkolemManager()->mkDummySkolem("e", stn);
  }
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
