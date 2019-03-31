/*********************                                                        */
/*! \file inst_explain.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of instantiate
 **/

#include "theory/quantifiers/inst_explain.h"

#include "options/quantifiers_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void InstExplainLit::initialize(Node inst)
{
  d_this = inst;
}
void InstExplainLit::reset()
{
  d_curr_prop_insts.clear();
}
void InstExplainLit::addInstExplanation(Node inst)
{
  if (std::find(d_insts.begin(), d_insts.end(), inst) == d_insts.end())
  {
    d_insts.push_back(inst);    
  }
}

void InstExplainLit::setPropagating(Node inst)
{
  Assert( std::find(d_curr_prop_insts.begin(),d_curr_prop_insts.end(),inst)==d_curr_prop_insts.end() );
  Assert( std::find(d_inst.begin(),d_inst.end(),inst)!=d_inst.end());
  d_curr_prop_insts.push_back(inst);
  // TODO: get the explanation?
}

void InstExplainInst::initialize(Node inst)
{
  d_this = inst;
}

void InstExplainInst::propagate( QuantifiersEngine * qe, std::vector< Node >& propLits )
{
  // if possible, propagate the literal in the clause that must be true
  std::unordered_set<Node, NodeHashFunction> visited;
  std::vector<Node> visit;
  std::map< Node, bool > ecache;
  Node cur;
  visit.push_back(d_this);
  do
  {
    cur = visit.back();
    visit.pop_back();
    // cur should hold in the current context
    Assert( evaluate(cur,ecache,qe) );
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      TNode atom = cur.getKind() == NOT ? cur[0] : cur;
      bool pol = cur.getKind() != NOT;
      Kind k = atom.getKind();
      if (k == AND || k==OR)
      {
        if( (k==AND)==pol )
        {
          for( const Node& nc : cur )
          {
            visit.push_back(pol ? nc : nc.negate());
          }
        }
        else
        {
          // propagate the one if all others are false
          Node trueLit;
          for( const Node& nc : cur )
          {
            if( evaluate(nc,ecache,qe)==pol )
            {
              if( trueLit.isNull() )
              {
                trueLit = nc;
              }
              else
              {
                trueLit = Node::null();
                break;
              }
            }
          }
          if( !trueLit.isNull() )
          {
            visit.push_back(trueLit);
          }
        }
      }
      else if (k == ITE)
      {
        // get polarity of the head
        //   T  T F ----> ~2 propagate B, 1
        //   T  F T ----> ~1 propagate B, 2
        //   T  T T ----> nothing
        for( unsigned i=0; i<2; i++ )
        {
          if( evaluate(cur[i+1],ecache,qe)!=pol )
          {
            visit.push_back(pol ? cur[2-i] : cur[2-i].negate());
            visit.push_back(i==0 ? cur[0].negate() : cur[0] );
          }
        }
      }
      else if (k == EQUAL && atom[0].getType().isBoolean())
      {
        //   T T ---> 1 propagate 2  +  2 propagate 1
        // ????
      }
      else
      {
        // propagates
        propLits.push_back(cur);
      }
    }
  } while (!visit.empty());
}

bool InstExplainInst::evaluate( Node n, std::map< Node, bool >& ecache, QuantifiersEngine * qe )
{
  
  /*
  std::vector<TNode> visit;
  visit.push_back(n);
  TNode cur;
  do
  {
    cur = visit.back();
    visit.pop_back();
    if( ecache.find(n)==ecache.end() )
    {
      
    }
  }while( !visit.empty() );
  return ecache[n];
  */
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
