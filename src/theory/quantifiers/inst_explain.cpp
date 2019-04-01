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
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
void IeEvaluator::reset()
{
  d_ecache.clear();
}

int IeEvaluator::evaluate(Node n)
{
  std::map<Node, int>::iterator it = d_ecache.find(n);
  if (it != d_ecache.end())
  {
    return it->second;
  }
  Kind k = n.getKind();
  if (k == NOT)
  {
    return -evaluate(n[0]);
  }
  int res = 0;
  if (k == AND || k == OR)
  {
    int expv = (k == OR) ? 1 : -1;
    for (TNode nc : n)
    {
      int cres = evaluate(nc);
      if (cres == expv || cres==0)
      {
        d_ecache[n] = expv;
        return expv;
      }
    }
    res = -expv;
  }
  else if (k == ITE)
  {
    unsigned checkIndex = evaluate(n[0]) ? 1 : 2;
    res = evaluate(n[checkIndex]);
  }
  else if (k == EQUAL && n[0].getType().isBoolean())
  {
    res = evaluate(n[0]) == evaluate(n[1]);
  }
  else
  {
    // lookup the value in the valuation
    bool bres;
    if (d_valuation.hasSatValue(n, bres))
    {
      res = bres ? 1 : -1;
    }
  }
  d_ecache[n] = res;
  return res;
}

void InstExplainLit::initialize(Node inst) { d_this = inst; }
void InstExplainLit::reset() { d_curr_prop_exps.clear(); }
void InstExplainLit::addInstExplanation(Node inst)
{
  if (std::find(d_insts.begin(), d_insts.end(), inst) == d_insts.end())
  {
    d_insts.push_back(inst);
  }
}

void InstExplainLit::setPropagating(Node inst)
{
  Assert(std::find(d_insts.begin(), d_insts.end(), inst) != d_insts.end());
  //  get the explanation
  std::map<Node, Node>::iterator it = d_inst_to_exp.find(inst);
  if (it == d_inst_to_exp.end())
  {
    bool pol = d_this.getKind() != NOT;
    TNode atomt = pol ? d_this : d_this[0];
    TNode constt = NodeManager::currentNM()->mkConst(!pol);
    Node instn = TermUtil::simpleNegate(inst);
    Node instns = instn.substitute(atomt, constt);
    instns = Rewriter::rewrite(instns);
    d_inst_to_exp[inst] = instns;
    d_curr_prop_exps.push_back(instns);
  }
  else
  {
    d_curr_prop_exps.push_back(it->second);
  }
}

void InstExplainInst::initialize(Node inst) { d_this = inst; }

void InstExplainInst::propagate(IeEvaluator& v,
                                std::vector<Node>& propLits)
{
  // if possible, propagate the literal in the clause that must be true
  std::unordered_set<Node, NodeHashFunction> visited;
  std::vector<Node> visit;
  Node cur;
  visit.push_back(d_this);
  do
  {
    cur = visit.back();
    visit.pop_back();
    // cur should hold in the current context
    Assert(v.evaluate(cur)==1);
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      Node atom = cur.getKind() == NOT ? cur[0] : cur;
      bool pol = cur.getKind() != NOT;
      Kind k = atom.getKind();
      if (k == AND || k == OR)
      {
        if ((k == AND) == pol)
        {
          // they all propagate
          for (const Node& nc : atom)
          {
            visit.push_back(pol ? nc : nc.negate());
          }
        }
        else
        {
          // propagate one if all others are false
          Node trueLit;
          for (const Node& nc : atom)
          {
            int cres = v.evaluate(nc);
            if( cres==0 )
            {
              // if one child is unknown, then there are no propagations
              trueLit = Node::null();
              break;
            }
            else if ((cres>0) == pol)
            {
              if (trueLit.isNull())
              {
                trueLit = nc;
              }
              else
              {
                // two literals are true, no propagations
                trueLit = Node::null();
                break;
              }
            }
          }
          if (!trueLit.isNull())
          {
            visit.push_back(pol ? trueLit : trueLit.negate());
          }
        }
      }
      else if (k == ITE)
      {
        // get polarity of the head
        //   T  T F ----> ~2 propagate B, 1
        //   T  T T ----> nothing
        //   T  T ? ----> nothing
        //   T  F T ----> ~1 propagate ~B, 2
        //   ....
        int cbres = v.evaluate(atom[0]);
        // only propagation if branch evaluates to true
        if( cbres!=0 )
        {
          for (unsigned i = 0; i < 2; i++)
          {
            int cres = v.evaluate(atom[i + 1]);
            if( cres==0 )
            {
              // if one child is unknown, there are no propagations
              break;
            }
            else if ((cres>0) != pol)
            {
              visit.push_back(pol ? atom[2 - i] : atom[2 - i].negate());
              visit.push_back(i == 0 ? atom[0].negate() : atom[0]);
              break;
            }
          }
        }
      }
      else if (k == EQUAL && atom[0].getType().isBoolean())
      {
        //   T T ---> 1 propagate 2  +  2 propagate 1
        //   F F ---> ~1 propagate ~2  +  ~2 propagate ~1
        int cres = v.evaluate(atom[0]);
        // they must both have values
        Assert( cres!=0 );
        visit.push_back(cres>0 ? atom[0] : atom[0].negate());
        visit.push_back((cres>0) == pol ? atom[1] : atom[1].negate());
      }
      else
      {
        // propagates
        propLits.push_back(cur);
      }
    }
  } while (!visit.empty());
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
