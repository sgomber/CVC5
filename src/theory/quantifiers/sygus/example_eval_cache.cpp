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

Node ExampleEvalCache::addSearchVal(Node bv)
{
  std::vector< Node > subTerms;
  return addSearchVal(bv,subTerms);
}

Node ExampleEvalCache::addSearchVal(Node bv, 
                                           std::vector< Node >& subTerms)
{
  if (!d_indexSearchVals)
  {
    // not indexing search values
    return Node::null();
  }
  std::vector<Node> vals;
  evaluateVec(bv, vals, subTerms, true);
  Trace("sygus-pbe-debug") << "Add to trie..." << std::endl;
  Node ret = d_trie.addOrGetTerm(bv, vals);
  Trace("sygus-pbe-debug") << "...got " << ret << std::endl;
  // Clean up the cache data if necessary: if the enumerated term
  // is redundant, its cached data will not be used later and thus should
  // be cleared now.
  if (ret != bv)
  {
    // immediately clear it
    Trace("sygus-pbe-debug") << "...clear example cache" << std::endl;
    clearEvaluationCache(bv);
  }
  else
  {
    // should remember permanently
    NodeTrie * curr = &d_trie;
    for( size_t i=0, vsize = vals.size(); i<vsize; i++)
    {
      NodeTrie * next = &curr->d_data[vals[i]];
      d_revParent[next] = curr;
      d_revParentEdge[next] = vals[i];
      curr = next;
    }
    d_revLeaf[bv] = curr;
  }
  Assert(ret.getType().isComparableTo(bv.getType()));
  return ret;
}

void ExampleEvalCache::evaluateVec(Node bv,
                                   std::vector<Node>& exOut, 
                                   bool doCache)
{
  std::vector< Node > subTerms;
  evaluateVec(bv,exOut,subTerms,doCache);
}
void ExampleEvalCache::evaluateVec(Node bv,
                                   std::vector<Node>& exOut, 
                                   std::vector< Node >& subTerms, 
                                   bool doCache)
{
  // is it in the cache?
  std::map<Node, std::vector<Node>>::iterator it = d_exOutCache.find(bv);
  if (it != d_exOutCache.end())
  {
    exOut.insert(exOut.end(), it->second.begin(), it->second.end());
    return;
  }
  // get the evaluation
  evaluateVecInternal(bv, exOut, subTerms);
  // store in cache if necessary
  if (doCache)
  {
    std::vector<Node>& eocv = d_exOutCache[bv];
    eocv.insert(eocv.end(), exOut.begin(), exOut.end());
  }
}

void ExampleEvalCache::evaluateVecInternal(Node bv,
                                           std::vector<Node>& exOut, 
                                           std::vector< Node >& subTerms) const
{
  // use ExampleMinEval
  SygusTypeInfo& ti = d_tds->getTypeInfo(d_stn);
  const std::vector<Node>& varlist = ti.getVarList();
  EmeEvalTds emetds(d_tds, d_stn);
  ExampleMinEval eme(bv, varlist, &emetds);
  // lookup the evaluation for relevant arguments
  std::vector< std::unordered_map<Node, Node, NodeHashFunction> > visited;
  size_t esize = d_examples.size();
  visited.resize(esize);
  for (const Node& st : subTerms)
  {
    std::vector< Node > vals;
    if (lookupEvaluation(st,vals))
    {
      Trace("ajr-temp") << "Lookup evaluation for " << st << " returned " << vals << std::endl;
      Assert(vals.size()==esize);
      for (size_t j = 0; j < esize; j++)
      {
        visited[j][st] = vals[j];
      }
    }
  }
  for (size_t j = 0; j < esize; j++)
  {
    Node res = eme.evaluate(d_examples[j], visited[j]);
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

bool ExampleEvalCache::lookupEvaluation(Node n, std::vector< Node >& vals) const
{
  std::map< Node, NodeTrie * >::const_iterator itr = d_revLeaf.find(n);
  if (itr == d_revLeaf.end())
  {
    return false;
  }
  std::map< NodeTrie *, NodeTrie * >::const_iterator itp;
  std::map< NodeTrie *, Node >::const_iterator itd;
  NodeTrie * curr = itr->second;
  do
  {
    itp = d_revParent.find(curr);
    if (itp !=d_revParent.end())
    {
      itd = d_revParentEdge.find(curr);
      Assert(itd !=d_revParentEdge.end());
      vals.push_back(itd->second);
      curr = itp->second;
    }
  }while (itp !=d_revParent.end());
  std::reverse(vals.begin(),vals.end());
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
