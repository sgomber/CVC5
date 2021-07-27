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

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/datatypes_options.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "util/bitvector.h"

using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace preprocessing {
namespace passes {

SygusEnumeratorCallbackConstElim::SygusEnumeratorCallbackConstElim(
    Node e, const std::vector<Node>& cs)
    : theory::quantifiers::SygusEnumeratorCallback(e)
{
  for (const Node& c : cs)
  {
    d_solved[c] = Node::null();
  }
}

bool SygusEnumeratorCallbackConstElim::addTermInternal(Node n, Node bn, Node bnr)
{
  if (bn == bnr)
  {
    return true;
  }
  std::map<Node, Node>::iterator it = d_solved.find(bnr);
  if (it != d_solved.end())
  {
    if (it->second.isNull())
    {
      // does it eliminate?
      Node bns = d_subs.apply(bn);
      if (!expr::hasSubterm(bns, bnr))
      {
        Trace("analyze-solved")
            << "SOLVED: " << bnr << " <- " << bns << std::endl;
        d_solved[bnr] = bns;
        d_subs.add(bnr, bns);
      }
    }
  }
  return true;
}

AnalyzeConstants::AnalyzeConstants() {}

void AnalyzeConstants::analyzeConstants(TypeNode tn,
                                        const std::vector<Node>& cs)
{
  Trace("analyze-debug") << "Constants of type " << tn << ":" << std::endl;
  for (const Node& c : cs)
  {
    if (tn.isBitVector())
    {
      const BitVector& bv = c.getConst<BitVector>();
      Trace("analyze-debug") << "#b" << bv.toString() << std::endl;
    }
    else
    {
      Trace("analyze") << c << std::endl;
    }
  }
  if (tn.isBitVector())
  {
    uint32_t w = tn.getBitVectorSize();
    if (w <= 8 || cs.size() <= 1)
    {
      return;
    }
    Trace("analyze") << "Setting up sygus enumeration for " << cs.size()
                     << " constants for type " << tn << "..." << std::endl;
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
    SygusEnumeratorCallbackConstElim scce(e, cs);
    quantifiers::SygusEnumerator se(nullptr, &scce);
    se.initialize(e);
    size_t maxSize = options::sygusAbortSizeTest() >= 0
                         ? static_cast<size_t>(options::sygusAbortSizeTest())
                         : 3;
    while (se.increment())
    {
      Node curr = se.getCurrent();
      if (datatypes::utils::getSygusTermSize(curr) >= maxSize)
      {
        break;
      }
      if (!curr.isNull())
      {
        Trace("analyze-enum")
            << "  " << datatypes::utils::sygusToBuiltin(curr) << std::endl;
      }
    }
    Trace("analyze") << "...finished enumeration" << std::endl;
    Trace("analyze") << "Constants of type " << tn << ":" << std::endl;
    size_t solvedCount = 0;
    std::unordered_set<uint32_t> bitTrans;
    bitTrans.insert(0);
    for (const Node& c : cs)
    {
      const BitVector& bv = c.getConst<BitVector>();
      Trace("analyze") << "#b" << bv.toString();
      if (scce.d_solved[c].isNull())
      {
        Trace("analyze") << " (req)";
        bool currBitSet = bv.isBitSet(0);
        for (uint32_t i = 1; i < w; i++)
        {
          if (bv.isBitSet(i) != currBitSet)
          {
            bitTrans.insert(i);
            currBitSet = !currBitSet;
          }
        }
      }
      else
      {
        solvedCount++;
      }
      Trace("analyze") << std::endl;
    }
    Trace("analyze") << solvedCount << " / " << cs.size() << " constants solved"
                     << std::endl;
    Trace("analyze") << bitTrans.size() << " / " << w
                     << " bits have transitions" << std::endl;
    for (uint32_t i = 0; i < w; i++)
    {
      Trace("analyze") << (bitTrans.find((w - i) - 1) != bitTrans.end() ? 1
                                                                        : 0);
    }
    Trace("analyze") << std::endl;
  }
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
