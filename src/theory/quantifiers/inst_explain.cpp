/*********************                                                        */
/*! \file inst_explain.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of instantiate
 **/

#include "theory/quantifiers/inst_explain.h"

#include "theory/quantifiers/term_util.h"
#include "theory/valuation.h"
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
  d_curr_prop_exps.clear();
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
  Assert( std::find(d_insts.begin(),d_insts.end(),inst)!=d_insts.end());
  //  get the explanation
  std::map< Node, Node >::iterator it = d_inst_to_exp.find(inst);
  if( it==d_inst_to_exp.end() )
  {
    bool pol = d_this.getKind()!=NOT;
    TNode atomt = pol ? d_this : d_this[0];
    TNode constt = NodeManager::currentNM()->mkConst(!pol);
    Node instn = TermUtil::simpleNegate(inst);
    Node instns = instn.substitute(atomt,constt);
    instns = Rewriter::rewrite(instns);
    d_inst_to_exp[inst] = instns;
    d_curr_prop_exps.push_back(instns);
  }
  else
  {
    d_curr_prop_exps.push_back(it->second);
  }
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
  std::map< TNode, bool > ecache;
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
      Node atom = cur.getKind() == NOT ? cur[0] : cur;
      bool pol = cur.getKind() != NOT;
      Kind k = atom.getKind();
      if (k == AND || k==OR)
      {
        if( (k==AND)==pol )
        {
          // they all propagate
          for( const Node& nc : atom )
          {
            visit.push_back(pol ? nc : nc.negate());
          }
        }
        else
        {
          // propagate one if all others are false
          Node trueLit;
          for( const Node& nc : atom )
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
            visit.push_back(pol ? trueLit : trueLit.negate());
          }
        }
      }
      else if (k == ITE)
      {
        // get polarity of the head
        //   T  T F ----> ~2 propagate B, 1
        //   T  F T ----> ~1 propagate ~B, 2
        //   T  T T ----> nothing
        for( unsigned i=0; i<2; i++ )
        {
          if( evaluate(atom[i+1],ecache,qe)!=pol )
          {
            visit.push_back(pol ? atom[2-i] : atom[2-i].negate());
            visit.push_back(i==0 ? atom[0].negate() : atom[0] );
          }
        }
      }
      else if (k == EQUAL && atom[0].getType().isBoolean())
      {
        //   T T ---> 1 propagate 2  +  2 propagate 1
        //   F F ---> ~1 propagate ~2  +  ~2 propagate ~1
        bool res = evaluate( atom[0], ecache, qe );
        visit.push_back(res ? atom[0] : atom[0].negate());
        visit.push_back(res==pol ? atom[1] : atom[1].negate());
      }
      else
      {
        // propagates
        propLits.push_back(cur);
      }
    }
  } while (!visit.empty());
}

bool InstExplainInst::evaluate( TNode n, std::map< TNode, bool >& ecache, QuantifiersEngine * qe )
{
  std::map< TNode, bool >::iterator it = ecache.find(n);
  if( it!=ecache.end() )
  {
    return it->second;
  }
  Kind k = n.getKind();
  if( k==NOT )
  {
    return !evaluate(n[0],ecache,qe);
  }
  bool res = false;
  if( k==AND || k==OR )
  {
    bool expv = (k==OR);
    for( TNode nc : n )
    {
      if( evaluate(nc,ecache,qe)==expv )
      {
        ecache[n] = expv;
        return expv;
      }
    }
    res = !expv;
  }
  else if( k==ITE )
  {
    unsigned checkIndex = evaluate(n[0],ecache,qe) ? 1 : 2;
    res = evaluate(n[checkIndex],ecache,qe);
  }
  else if (k == EQUAL && n[0].getType().isBoolean())
  {
    res = evaluate(n[0],ecache,qe)==evaluate(n[1],ecache,qe);
  }
  else
  {
    // lookup the value in the valuation
    Valuation& v = qe->getValuation();
    if( !v.hasSatValue(n,res) )
    {
      AlwaysAssert(false);
    }
  }
  ecache[n] = res;
  return res;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
