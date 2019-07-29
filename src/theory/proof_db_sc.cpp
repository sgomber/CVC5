/*********************                                                        */
/*! \file proof_db_sc.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof side conditions
 **/

#include "theory/proof_db_sc.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

ProofDbScEval::ProofDbScEval()
{
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_negOne = NodeManager::currentNM()->mkConst(Rational(-1));
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);

  d_symTable[std::string("flatten_string")] = sc_flatten_string;
  d_symTable[std::string("re_loop_elim")] = sc_re_loop_elim;
  d_symTable[std::string("arith_norm_term")] = sc_arith_norm_term;
  d_symTable[std::string("arith_norm_term_abs")] = sc_arith_norm_term_abs;
  d_symTable[std::string("flatten_bool")] = sc_flatten_bool;
}

bool ProofDbScEval::registerSideCondition(Node sc)
{
  return buildOperatorTable(sc);
}

bool ProofDbScEval::buildOperatorTable(Node n)
{
  bool ret = false;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      // if it is APPLY_UF, we check if it is a side condition
      if (cur.getKind() == APPLY_UF)
      {
        ret = true;
        Node op = cur.getOperator();
        std::map<Node, SideConditionId>::iterator ito = d_opTable.find(op);
        // if not already processed
        if (ito == d_opTable.end())
        {
          std::stringstream ss;
          ss << op;
          Trace("proof-db-sc-init") << "Initialize side condition symbol "
                                    << ss.str() << "..." << std::endl;
          std::map<std::string, SideConditionId>::iterator it =
              d_symTable.find(ss.str());
          if (it != d_symTable.end())
          {
            Trace("proof-db-sc-init")
                << "*** Associate " << op << " / " << it->second << std::endl;
            d_opTable[op] = it->second;
          }
          else
          {
            Warning() << "Could not find side condition for operator " << op
                      << std::endl;
            AlwaysAssert(false);
          }
        }
      }
      // can be nested
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());
  return ret;
}

Node ProofDbScEval::evaluate(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = Node::null();
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
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (cur.getKind() == APPLY_UF)
      {
        ret = evaluateApp(cur.getOperator(), children);
        if (ret.isNull())
        {
          // failed side condition
          return ret;
        }
      }
      else if (childChanged)
      {
        if (cur.getMetaKind() == metakind::PARAMETERIZED)
        {
          children.insert(children.begin(), cur.getOperator());
        }
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node ProofDbScEval::evaluateApp(Node op, const std::vector<Node>& args)
{
  std::map<Node, SideConditionId>::iterator it = d_opTable.find(op);
  if (it == d_opTable.end())
  {
    Warning() << "Could not find side condition for operator " << op
              << " during evaluation" << std::endl;
    AlwaysAssert(false);
    return Node::null();
  }
  // ----------------------------- specific lookup into side conditions
  Trace("proof-db-sc") << "Run side condition " << it->second << " with args "
                       << args << std::endl;
  SideConditionId sid = it->second;
  Node ret;
  if (sid == sc_flatten_string)
  {
    Assert(args.size() == 1);
    ret = flatten_string(args[0]);
  }
  else if (sid == sc_re_loop_elim)
  {
    Assert(args.size() == 1);
    ret = re_loop_elim(args[0]);
  }
  else if (sid == sc_arith_norm_term)
  {
    Assert(args.size() == 1);
    ret = arith_norm_term(args[0]);
  }
  else if (sid == sc_arith_norm_term_abs)
  {
    Assert(args.size() == 1);
    ret = arith_norm_term_abs(args[0]);
  }
  else if (sid == sc_flatten_bool)
  {
    Assert(args.size() == 1);
    ret = flatten_bool(args[0]);
  }
  else
  {
    Warning() << "Unknown side condition id " << it->second << " for operator "
              << op << std::endl;
  }
  Trace("proof-db-sc") << "Side condition returned " << ret << std::endl;
  return ret;
}

bool ProofDbScEval::isSideConditionOp(Node op) const
{
  return d_opTable.find(op) != d_opTable.end();
}

////// side conditions

Node ProofDbScEval::h_flattenCollect(Kind k, Node n, Node acc)
{
  Kind nk = n.getKind();
  if (nk == k)
  {
    Node ret = h_flattenCollect(k, n[1], acc);
    return h_flattenCollect(k, n[0], ret);
  }
  // is zero element?
  bool isZeroElement = false;
  if (k==STRING_CONCAT)
  {
    isZeroElement = (nk == CONST_STRING && n.getConst<String>().size() == 0);
  }
  else if( k==AND )
  {
    isZeroElement = (n==d_true);
  }
  else if( k==OR )
  {
    isZeroElement = (n==d_false);
  }
  if (isZeroElement)
  {
    return acc;
  }
  if (acc.isNull())
  {
    return n;
  }
  else
  {
    return NodeManager::currentNM()->mkNode(k, n, acc);
  }
}
Node ProofDbScEval::flatten_string(Node n)
{
  Assert(n.getNumChildren() == 2);
  Node acc;
  return h_flattenCollect(n.getKind(), n, acc);
}
Node ProofDbScEval::flatten_bool(Node n)
{
  Assert(n.getNumChildren() == 2);
  Node acc;
  return h_flattenCollect(n.getKind(), n, acc);
}

Node ProofDbScEval::re_loop_elim(Node n)
{
  // TODO
  return n;
}

void ProofDbScEval::h_termToMsum(Node n, std::map<Node, Node>& msum)
{
  Assert(msum.empty());
  NodeManager* nm = NodeManager::currentNM();
  Kind nk = n.getKind();
  if (nk == PLUS || nk == MINUS)
  {
    Assert(n.getNumChildren() == 2);
    h_termToMsum(n[0], msum);
    std::map<Node, Node> msumOp;
    h_termToMsum(n[1], msumOp);
    std::map<Node, Node>::iterator it;
    for (std::pair<const Node, Node>& m : msumOp)
    {
      Node x = m.first;
      it = msum.find(x);
      Rational r2 = m.second.getConst<Rational>();
      if (nk == MINUS)
      {
        r2 = -r2;
      }
      if (it == msum.end())
      {
        msum[x] = nm->mkConst(r2);
        continue;
      }
      Rational r1 = it->second.getConst<Rational>();
      msum[x] = nm->mkConst(r1 + r2);
    }
  }
  else if (nk == UMINUS)
  {
    h_termToMsum(n[0], msum);
    for (std::pair<const Node, Node>& m : msum)
    {
      msum[m.first] = nm->mkConst(-m.second.getConst<Rational>());
    }
  }
  else if (nk == MULT)
  {
    Node c;
    if (n[0].isConst())
    {
      c = n[0];
      h_termToMsum(n[1], msum);
    }
    else if (n[1].isConst())
    {
      c = n[1];
      h_termToMsum(n[1], msum);
    }
    else
    {
      msum[n] = d_one;
    }
    if (!c.isNull())
    {
      Rational cr = c.getConst<Rational>();
      for (std::pair<const Node, Node>& m : msum)
      {
        msum[m.first] = nm->mkConst(m.second.getConst<Rational>() * cr);
      }
    }
  }
  else if (nk == CONST_RATIONAL)
  {
    msum[d_one] = n;
  }
  else
  {
    msum[n] = d_one;
  }
}

Node ProofDbScEval::h_msumToTerm(std::map<Node, Node>& msum,
                                 bool posLeadingCoeff)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> sums;
  bool isNeg = false;
  Node curr;
  for (std::pair<const Node, Node>& m : msum)
  {
    // zero, ignore
    if (m.second == d_zero)
    {
      continue;
    }
    Node x = m.first;
    // process positive leading coefficient requirement
    if (posLeadingCoeff && m.second.getConst<Rational>().sgn() < 0)
    {
      isNeg = true;
    }
    posLeadingCoeff = false;
    // if it is negated
    Node c = m.second;
    Assert(c.getKind() == CONST_RATIONAL);
    if (isNeg)
    {
      c = nm->mkConst(-c.getConst<Rational>());
    }
    // process
    Node t;
    if (c == d_one)
    {
      t = x;
    }
    else if (x == d_one)
    {
      t = c;
    }
    else
    {
      t = nm->mkNode(MULT, c, x);
    }
    if (curr.isNull())
    {
      curr = t;
    }
    else
    {
      curr = nm->mkNode(PLUS, t, curr);
    }
  }
  if (curr.isNull())
  {
    return d_zero;
  }
  return curr;
}

Node ProofDbScEval::arith_norm_term(Node n)
{
  // convert to monomial sum
  std::map<Node, Node> msum;
  h_termToMsum(n, msum);
  // then, back to term
  return h_msumToTerm(msum);
}

Node ProofDbScEval::arith_norm_term_abs(Node n)
{
  // convert to monomial sum
  std::map<Node, Node> msum;
  h_termToMsum(n, msum);
  // flip sign if leading coefficient is negative
  return h_msumToTerm(msum, true);
}

}  // namespace theory
}  // namespace CVC4
