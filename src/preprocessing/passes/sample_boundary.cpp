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
  std::unordered_map<Node, unsigned, NodeHashFunction> hasSampling;
  std::unordered_map<Node, bool, NodeHashFunction> isSampling;
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Trace("sample-boundary")
        << "Process sample boundary " << (*assertionsToPreprocess)[i] << "..."
        << std::endl;
    Node aip = convert(
        (*assertionsToPreprocess)[i], hasSampling, isSampling);
    Trace("sample-boundary") << "...got : " << aip << std::endl;
    assertionsToPreprocess->replace(i, aip);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

Node SampleBoundary::convert(
    TNode n,
    std::unordered_map<Node, unsigned, NodeHashFunction>& hasSampling,
    std::unordered_map<Node, bool, NodeHashFunction>& isSampling)
{
  NodeManager* nm = NodeManager::currentNM();
  
  std::unordered_map<Node, unsigned, TNodeHashFunction>::iterator iths;
  std::unordered_map<Node, bool, TNodeHashFunction>::iterator itfs;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  // compute has sampling / free sampling
  do
  {
    cur = visit.back();
    visit.pop_back();
    iths = hasSampling.find(cur);

    if (iths == hasSampling.end())
    {
      hasSampling[cur] = 0;
      visit.push_back(cur);
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
    else
    {
      itfs = isSampling.find(cur);
      if (itfs==isSampling.end())
      {
        Trace("sample-boundary-debug") << "sb::isSampling " << cur << "..." << std::endl;
        unsigned childHasSampleCount = 0;
        for (const Node& cn : cur)
        {
          // does the child have sampling?
          itfs = isSampling.find(cn);
          Assert(itfs != isSampling.end());
          if (itfs->second)
          {
            childHasSampleCount++;
          }
        }
        hasSampling[cur] = childHasSampleCount;
        isSampling[cur] = childHasSampleCount>0 || cur.getKind()==SAMPLE_RUN;
        Trace("sample-boundary-debug") << "  isSampling: " << hasSampling[cur] << " " << isSampling[cur] << std::endl;
      }
    }
  } while (!visit.empty());
  
  // now, go back and rebuild the node, adding SAMPLE_CHECK at the proper places
  std::unordered_map<Node, Node, TNodeHashFunction>::iterator it;
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  visit.push_back(n);
  // compute has sampling / free sampling
  do
  {
    cur = visit.back();
    Trace("sample-boundary-debug") << "sb::set boundaries " << cur << std::endl;
    Assert( cur.getType().isBoolean() );
    visit.pop_back();
    it = cache.find(cur);
    
    if( it==cache.end() )
    {
      itfs = isSampling.find(cur);
      Assert(itfs != isSampling.end());
      if( !itfs->second )
      {
        // no sampling in this node, no-op
        cache[cur] = cur;
      }
      else
      {
        iths = hasSampling.find(cur);
        Assert(iths != hasSampling.end());
        if( cur.getKind()==FORALL )
        {
          cache[cur] = Node::null();
          visit.push_back(cur);
          for( unsigned i=0, size=cur.getNumChildren(); i<size; i++ )
          {
            if( i==1 )
            {
              visit.push_back(cur[i]);
            }
            else
            {
              cache[cur[i]] = cur[i];
            }
          }
        }
        else
        {
          // can we miniscope?
          bool doMiniscope = false;
          if( cur.getKind()==AND )
          {
            doMiniscope = true;
          }
          else if( ( cur.getKind()==OR || cur.getKind()==IMPLIES ) && iths->second==1 )
          {
            doMiniscope = true;
          }
          
          if( doMiniscope )
          {
            cache[cur] = Node::null();
            visit.push_back(cur);
            for( const Node& cc : cur )
            {
              visit.push_back( cc );
            }
          }
          else
          {
            // no miniscoping possible, add sample check
            cache[cur] = nm->mkNode( SAMPLE_CHECK, cur );
          }
        }
      }
    }
    else if( it->second.isNull() )
    {
      std::vector< Node > children;
      if( cur.getMetaKind()==metakind::PARAMETERIZED )
      {
        children.push_back( cur.getOperator() );
      }
      for( const Node& cc : cur )
      {
        it = cache.find(cc);
        Assert( it!=cache.end() );
        children.push_back( it->second );
      }
      cache[cur] = nm->mkNode( cur.getKind(), children );
    }
  }while( !visit.empty() );
  
  Assert(cache.find(n) != cache.end());
  Assert(!cache.find(n)->second.isNull());
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
