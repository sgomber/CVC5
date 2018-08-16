/*********************                                                        */
/*! \file sample_boundary.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sample boundary
 **/

#include "preprocessing/passes/sample_boundary.h"

#include "theory/sample/theory_sample_rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {

SampleBoundary::SampleBoundary(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "sample-boundary"){};

PreprocessingPassResult SampleBoundary::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  std::unordered_map<Node, bool, NodeHashFunction> hasSampling;
  std::unordered_map<Node, bool, NodeHashFunction> isFreeSampling;
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Trace("sample-boundary")
        << "Process sample boundary " << (*assertionsToPreprocess)[i] << "..."
        << std::endl;
    Node aip = convert((*assertionsToPreprocess)[i], cache, hasSampling, isFreeSampling);
    Trace("sample-boundary") << "...got : " << aip << std::endl;
    assertionsToPreprocess->replace(i, aip);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

Node SampleBoundary::convert(
    TNode n,
    std::unordered_map<Node, Node, NodeHashFunction>& cache,
    std::unordered_map<Node, bool, NodeHashFunction>& hasSampling,
    std::unordered_map<Node, bool, NodeHashFunction>& isFreeSampling)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, Node, TNodeHashFunction>::iterator it;
  std::unordered_map<Node, bool, TNodeHashFunction>::iterator itfs;
  std::unordered_map<Node, bool, TNodeHashFunction>::iterator iths;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = cache.find(cur);

    if (it == cache.end())
    {
      cache[cur] = Node::null();
      visit.push_back(cur);
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      bool isFreeSample =
          theory::sample::TheorySampleRewriter::isSampleType(cur.getType());
      unsigned childHasSampleCount = 0;
      bool isBoolConnective = isBoolConnectiveTerm(cur);
      for (const Node& cn : cur)
      {
        it = cache.find(cn);
        Assert(it != cache.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        // does the child have free occurrences of sampling?
        itfs = isFreeSampling.find(cn);
        Assert(itfs != isFreeSampling.end());
        // does the child have sampling?
        iths = hasSampling.find(cn);
        Assert(iths != hasSampling.end());
        if( iths->second )
        {
          childHasSampleCount++;
        }
        // if we are a Boolean connective and the child has free sampling, make
        // the child into a sample literal
        if (isBoolConnective && itfs->second)
        {
          childChanged = true;
          Node scn = nm->mkNode(SAMPLE_CHECK, it->second);
          children.push_back(scn);
        }
        else
        {
          // otherwise, track
          children.push_back(it->second);
          isFreeSample = isFreeSample || itfs->second;
        }
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      hasSampling[cur] = childHasSampleCount>0 || isFreeSample;
      isFreeSampling[cur] = isFreeSample;
      // If we are a Boolean connective that is not AND, then we can have
      // at most one child with sampling. If we have more than one, we make this
      // entire formula into a sampling formula.
      if( childHasSampleCount>1 && cur.getKind()!=AND )
      {
        ret = nm->mkNode(SAMPLE_CHECK, cur);
      }
      cache[cur] = ret;
    }
  } while (!visit.empty());
  Assert(cache.find(n) != cache.end());
  Assert(!cache.find(n)->second.isNull());
  // top-level literal
  if (isFreeSampling[n])
  {
    cache[n] = nm->mkNode(SAMPLE_CHECK, n);
  }
  return cache[n];
}

bool SampleBoundary::isBoolConnective(Kind k)
{
  return k == OR || k == AND || k == EQUAL || k == ITE || k == NOT
         || k == IMPLIES || k == XOR;
}

bool SampleBoundary::isBoolConnectiveTerm(TNode n)
{
  return isBoolConnective(n.getKind())
         && (n.getKind() != EQUAL || n[0].getType().isBoolean())
         && (n.getKind() != ITE || n.getType().isBoolean());
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
