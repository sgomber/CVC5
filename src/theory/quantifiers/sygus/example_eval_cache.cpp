/*********************                                                        */
/*! \file example_eval_cache.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **/
#include "theory/quantifiers/sygus/example_eval_cache.h"

#include "theory/quantifiers/sygus/example_min_eval.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

ExampleEvalCache::ExampleEvalCache(TermDbSygus* tds,
                                   SynthConjecture* p,
                                   Node f,
                                   Node e)
    : d_tds(tds), d_stn(e.getType())
{
  ExampleInfer* ei = p->getExampleInfer();
  Assert(ei->hasExamples(f));
  for (unsigned i = 0, nex = ei->getNumExamples(f); i < nex; i++)
  {
    std::vector<Node> input;
    ei->getExample(f, i, input);
    d_examples.push_back(input);
  }
  d_indexSearchVals = !d_tds->isVariableAgnosticEnumerator(e);
}

ExampleEvalCache::~ExampleEvalCache() {}

Node ExampleEvalCache::addSearchVal(Node n, Node bv)
{
  if (!d_indexSearchVals)
  {
    // not indexing search values
    return Node::null();
  }

  std::vector<Node> vals;
  evaluateVec(n, bv, vals, true);
  Trace("sygus-pbe-debug") << "Add to trie..." << std::endl;
  Node ret = d_trie.addOrGetTerm(bv, vals);
  Trace("sygus-pbe-debug") << "...got " << ret << std::endl;
  // Only save the cache data if necessary: if the enumerated term
  // is redundant, its cached data will not be used later and thus should
  // be discarded. This applies also to the case where the evaluation
  // was cached prior to this call.
  if (ret != bv)
  {
    clearEvaluationCache(bv);
  }
  Assert(ret.getType().isComparableTo(bv.getType()));
  return ret;
}

void ExampleEvalCache::evaluateVec(Node bv, std::vector<Node>& exOut)
{
  evaluateVecInternal(Node::null(),bv,exOut);
}

void ExampleEvalCache::evaluateVec(Node n, Node bv, std::vector<Node>& exOut, bool doCache)
{
  // is it in the cache?
  std::map<Node, std::vector<Node>>::iterator it = d_exOutCache.find(n);
  if (it != d_exOutCache.end())
  {
    exOut.insert(exOut.end(), it->second.begin(), it->second.end());
    return;
  }
  // get the evaluation
  evaluateVecInternal(n, bv, exOut);
  // store in cache if necessary
  if (doCache)
  {
    std::vector<Node>& eocv = d_exOutCache[n];
    eocv.insert(eocv.end(), exOut.begin(), exOut.end());
  }
}

void ExampleEvalCache::evaluateVecInternal(Node n, 
                                           Node bv,
                                           std::vector<Node>& exOut)
{

  // use ExampleMinEval
  SygusTypeInfo& ti = d_tds->getTypeInfo(d_stn);
  const std::vector<Node>& varlist = ti.getVarList();
  EmeEvalTds emetds(d_tds, d_stn);
  ExampleMinEval eme(bv, varlist, &emetds);
  std::vector< std::map< Node, std::vector<Node> >::iterator > vecIt;
  VariadicTrieEval * vte = nullptr;
  if (!n.isNull() && n.getNumChildren()>0)
  {
    vte = &(d_vteCache[n.getOperator()]);
    for (const Node& nc : n)
    {
      std::map< Node, std::vector<Node> >::iterator it = d_exOutCache.find(nc);
      vecIt.push_back(it);
    }
  }
  for (size_t j = 0, esize = d_examples.size(); j < esize; j++)
  {
    Node res;
    if (vte!=nullptr)
    {
      VariadicTrieEval * vteCurr = vte;
      for (const std::map< Node, std::vector<Node> >::iterator& it : vecIt)
      {
        vteCurr = &(vteCurr->d_children[it->second[j]]);
      }
      res = vteCurr->d_data;
      if (res.isNull())
      {
        res = eme.evaluate(d_examples[j]);
        vteCurr->d_data = res;
      }
    }
    else
    {
      res = eme.evaluate(d_examples[j]);
    }
    exOut.push_back(res);
  }
}

Node ExampleEvalCache::evaluate(Node bn, unsigned i) const
{
  Assert(i < d_examples.size());
  return d_tds->evaluateBuiltin(d_stn, bn, d_examples[i]);
}

void ExampleEvalCache::clearEvaluationCache(Node bv)
{
  Assert(d_exOutCache.find(bv) != d_exOutCache.end());
  d_exOutCache.erase(bv);
}

void ExampleEvalCache::clearEvaluationAll() { d_exOutCache.clear(); }

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
