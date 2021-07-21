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

#include "preprocessing/util/analyze_constants.h"

#include "expr/skolem_manager.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "util/bitvector.h"

using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace preprocessing {
namespace passes {

AnalyzeConstants::AnalyzeConstants(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "analyze")
{
}


void AnalyzeConstants::analyzeConstants(TypeNode tn, const std::vector<Node>& cs)
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
    Trace("analyze") << "Setting up sygus enumeration..." << std::endl;
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
    quantifiers::SygusEnumerator se;
    se.initialize(e);
    size_t counter = 0;
    while (counter < 1000 && se.increment())
    {
      Node curr = se.getCurrent();
      if (!curr.isNull())
      {
        Trace("analyze") << "  " << curr << std::endl;
      }
    }
  }
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
