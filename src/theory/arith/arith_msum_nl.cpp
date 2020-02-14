/*********************                                                        */
/*! \file arith_msum_nl.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of arith_msum
 **/

#include "theory/arith/arith_msum_nl.h"

#include "theory/arith/arith_msum.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

bool isMult(Node n)
{
  return n.getKind()==MULT || n.getKind()==NONLINEAR_MULT;
}
  
bool ArithMSumNl::getMonomial(Node var, Node n, Node& c)
{
  if (isMult(n))
  {
    bool foundVar = false;
    std::vector< Node > vars;
    for (const Node& nc : n)
    {
      if (nc==var)
      {
        if (foundVar)
        {
          // non-linear
          return false;
        }
        foundVar = true;
      }
      else
      {
        vars.push_back(nc);
      }
    }
    if (foundVar)
    {
      Assert( !vars.empty() );
      c = vars.size()==1 ? vars[0] : NodeManager::currentNM()->mkNode(MULT,vars);
      c = Rewriter::rewrite(c);
      return true;
    }
  }
  else if (n==var)
  {
    c = NodeManager::currentNM()->mkConst(Rational(1));
    return true;
  }
  return false;
}

bool ArithMSumNl::getMonomialAcc(Node var, Node n, Node& coeff)
{
  Node c;
  if (getMonomial(var, n, c))
  {
    if (coeff.isNull())
    {
      coeff = n;
    }
    else
    {
      Node sum = NodeManager::currentNM()->mkNode(PLUS,coeff,n);
      coeff = Rewriter::rewrite(sum);
    }
    return true;
  }
  return false;
}

Node ArithMSumNl::solve(Node poly, Node var)
{
  Assert( poly.getType().isReal() );
  std::vector<Node> mons;
  if (poly.getKind()==PLUS)
  {
    for (const Node& pc : poly)
    {
      mons.push_back(pc);
    }
  }
  else
  {
    mons.push_back(poly);
  }
  
  NodeManager * nm = NodeManager::currentNM();
  std::vector<Node> sum;
  Node coeff;
  for (const Node& mc : mons)
  {
    if (!getMonomialAcc(var,mc,coeff))
    {
      sum.push_back(mc);
    }
  }
  if (coeff.isNull())
  {
    // does not contain
    return Node::null();
  }
  Node sol;
  if (sum.size()>1)
  {
    sol = nm->mkNode(PLUS, sum);
  }
  else
  {
    sol = sum.empty() ? nm->mkConst(Rational(0)) : sum[0];
  }
  sol = nm->mkNode(DIVISION, sol, coeff);
  sol = ArithMSum::negate(sol);
  sol = Rewriter::rewrite(sol);
  return sol;
}

Node ArithMSumNl::solveEqualityFor(Node lit, Node var)
{
  Assert(lit.getKind() == EQUAL);
  // first look directly at sides
  TypeNode tn = lit[0].getType();
  for (unsigned r = 0; r < 2; r++)
  {
    if (lit[r] == var)
    {
      return lit[1 - r];
    }
  }
  if (tn.isReal())
  {
    NodeManager * nm = NodeManager::currentNM();
    Node poly = nm->mkNode(MINUS, lit[0], lit[1]);
    poly = Rewriter::rewrite(poly);
    return solve(poly, var);
  }
  return Node::null();
}

} /* CVC4::theory namespace */
} /* CVC4 namespace */
