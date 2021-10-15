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
 * Implementation of entailment check class.
 */

#include "theory/quantifiers/entailment_check.h"

#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"

using namespace cvc5::kind;
using namespace cvc5::context;

namespace cvc5 {
namespace theory {
namespace quantifiers {

EntailmentCheck::EntailmentCheck(Env& env, QuantifiersState& qs, TermDb& tdb)
    : EnvObj(env), d_qstate(qs), d_tdb(tdb)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

EntailmentCheck::~EntailmentCheck() {}
Node EntailmentCheck::evaluateTerm2(TNode n,
                                    std::map<TNode, Node>& visited,
                                    std::vector<Node>& exp,
                                    bool useEntailmentTests,
                                    bool computeExp,
                                    bool reqHasTerm)
{
  std::map<TNode, Node>::iterator itv = visited.find(n);
  if (itv != visited.end())
  {
    return itv->second;
  }
  size_t prevSize = exp.size();
  Trace("term-db-eval") << "evaluate term : " << n << std::endl;
  Node ret = n;
  if (n.getKind() == FORALL || n.getKind() == BOUND_VARIABLE)
  {
    // do nothing
  }
  else if (d_qstate.hasTerm(n))
  {
    Trace("term-db-eval") << "...exists in ee, return rep" << std::endl;
    ret = d_qstate.getRepresentative(n);
    if (computeExp)
    {
      if (n != ret)
      {
        exp.push_back(n.eqNode(ret));
      }
    }
    reqHasTerm = false;
  }
  else if (n.hasOperator())
  {
    std::vector<TNode> args;
    bool ret_set = false;
    Kind k = n.getKind();
    std::vector<Node> tempExp;
    for (unsigned i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      TNode c = evaluateTerm2(
          n[i], visited, tempExp, useEntailmentTests, computeExp, reqHasTerm);
      if (c.isNull())
      {
        ret = Node::null();
        ret_set = true;
        break;
      }
      else if (c == d_true || c == d_false)
      {
        // short-circuiting
        if ((k == AND && c == d_false) || (k == OR && c == d_true))
        {
          ret = c;
          ret_set = true;
          reqHasTerm = false;
          break;
        }
        else if (k == ITE && i == 0)
        {
          ret = evaluateTerm2(n[c == d_true ? 1 : 2],
                              visited,
                              tempExp,
                              useEntailmentTests,
                              computeExp,
                              reqHasTerm);
          ret_set = true;
          reqHasTerm = false;
          break;
        }
      }
      if (computeExp)
      {
        exp.insert(exp.end(), tempExp.begin(), tempExp.end());
      }
      Trace("term-db-eval") << "  child " << i << " : " << c << std::endl;
      args.push_back(c);
    }
    if (ret_set)
    {
      // if we short circuited
      if (computeExp)
      {
        exp.clear();
        exp.insert(exp.end(), tempExp.begin(), tempExp.end());
      }
    }
    else
    {
      // get the (indexed) operator of n, if it exists
      TNode f = d_tdb.getMatchOperator(n);
      // if it is an indexed term, return the congruent term
      if (!f.isNull())
      {
        // if f is congruent to a term indexed by this class
        TNode nn = d_tdb.getCongruentTerm(f, args);
        Trace("term-db-eval") << "  got congruent term " << nn
                              << " from DB for " << n << std::endl;
        if (!nn.isNull())
        {
          if (computeExp)
          {
            Assert(nn.getNumChildren() == n.getNumChildren());
            for (size_t i = 0, nchild = nn.getNumChildren(); i < nchild; i++)
            {
              if (nn[i] != n[i])
              {
                exp.push_back(nn[i].eqNode(n[i]));
              }
            }
          }
          ret = d_qstate.getRepresentative(nn);
          Trace("term-db-eval") << "return rep" << std::endl;
          ret_set = true;
          reqHasTerm = false;
          Assert(!ret.isNull());
          if (computeExp)
          {
            if (n != ret)
            {
              exp.push_back(nn.eqNode(ret));
            }
          }
        }
      }
      if (!ret_set)
      {
        Trace("term-db-eval") << "return rewrite" << std::endl;
        // a theory symbol or a new UF term
        if (n.getMetaKind() == metakind::PARAMETERIZED)
        {
          args.insert(args.begin(), n.getOperator());
        }
        ret = NodeManager::currentNM()->mkNode(n.getKind(), args);
        ret = rewrite(ret);
        if (ret.getKind() == EQUAL)
        {
          if (d_qstate.areDisequal(ret[0], ret[1]))
          {
            ret = d_false;
          }
        }
        if (useEntailmentTests)
        {
          if (ret.getKind() == EQUAL || ret.getKind() == GEQ)
          {
            Valuation& val = d_qstate.getValuation();
            for (unsigned j = 0; j < 2; j++)
            {
              std::pair<bool, Node> et = val.entailmentCheck(
                  options::TheoryOfMode::THEORY_OF_TYPE_BASED,
                  j == 0 ? ret : ret.negate());
              if (et.first)
              {
                ret = j == 0 ? d_true : d_false;
                if (computeExp)
                {
                  exp.push_back(et.second);
                }
                break;
              }
            }
          }
        }
      }
    }
  }
  // must have the term
  if (reqHasTerm && !ret.isNull())
  {
    Kind k = ret.getKind();
    if (k != OR && k != AND && k != EQUAL && k != ITE && k != NOT
        && k != FORALL)
    {
      if (!d_qstate.hasTerm(ret))
      {
        ret = Node::null();
      }
    }
  }
  Trace("term-db-eval") << "evaluated term : " << n << ", got : " << ret
                        << ", reqHasTerm = " << reqHasTerm << std::endl;
  // clear the explanation if failed
  if (computeExp && ret.isNull())
  {
    exp.resize(prevSize);
  }
  visited[n] = ret;
  return ret;
}

TNode EntailmentCheck::getEntailedTerm2(TNode n)
{
  Trace("term-db-entail") << "get entailed term : " << n << std::endl;
  if (d_qstate.hasTerm(n))
  {
    Trace("term-db-entail") << "...exists in ee, return rep " << std::endl;
    return n;
  }
  else if (n.getKind() == BOUND_VARIABLE)
  {
    return TNode::null();
  }
  std::unordered_map<Node, TNode>::iterator itc = d_cacheEntailedTerm.find(n);
  if (itc!=d_cacheEntailedTerm.end())
  {
    return itc->second;
  }
  if (n.getKind() == ITE)
  {
    for (uint32_t i = 0; i < 2; i++)
    {
      if (isEntailed2(n[0], i == 0))
      {
        TNode ret = getEntailedTerm2(n[i == 0 ? 1 : 2]);
        d_cacheEntailedTerm[n] = ret;
        return ret;
      }
    }
  }
  else if (n.hasOperator())
  {
    TNode f = d_tdb.getMatchOperator(n);
    if (!f.isNull())
    {
      std::vector<TNode> args;
      for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
      {
        TNode c = getEntailedTerm2(n[i]);
        if (c.isNull())
        {
          d_cacheEntailedTerm[n] = TNode::null();
          return TNode::null();
        }
        c = d_qstate.getRepresentative(c);
        Trace("term-db-entail") << "  child " << i << " : " << c << std::endl;
        args.push_back(c);
      }
      TNode nn = d_tdb.getCongruentTerm(f, args);
      d_cacheEntailedTerm[n] = nn;
      Trace("term-db-entail")
          << "  got congruent term " << nn << " for " << n << std::endl;
      return nn;
    }
  }
  
  d_cacheEntailedTerm[n] = TNode::null();
  return TNode::null();
}

Node EntailmentCheck::evaluateTerm(TNode n,
                                   bool useEntailmentTests,
                                   bool reqHasTerm)
{
  std::map<TNode, Node> visited;
  std::vector<Node> exp;
  return evaluateTerm2(n, visited, exp, useEntailmentTests, false, reqHasTerm);
}

Node EntailmentCheck::evaluateTerm(TNode n,
                                   std::vector<Node>& exp,
                                   bool useEntailmentTests,
                                   bool reqHasTerm)
{
  std::map<TNode, Node> visited;
  return evaluateTerm2(n, visited, exp, useEntailmentTests, true, reqHasTerm);
}

TNode EntailmentCheck::getEntailedTerm(TNode n,
                                       std::map<TNode, TNode>& subs,
                                       bool subsRep)
{
  return getEntailedTerm2(n, subs, subsRep, true);
}

TNode EntailmentCheck::getEntailedTerm(TNode n)
{
  std::map<TNode, TNode> subs;
  return getEntailedTerm2(n, subs, false, false);
}

bool EntailmentCheck::isEntailed2(
    TNode n, bool pol)
{  
  std::unordered_map<Node, int >::iterator it = d_cacheEntailed.find(n);
  if (it !=d_cacheEntailed.end())
  {
    // must match
    return it->second==(pol ? 1 : -1);
  }
  Trace("term-db-entail") << "Check entailed : " << n << ", pol = " << pol
                          << std::endl;
  Assert(n.getType().isBoolean());
  Kind k = n.getKind();
  if (k == EQUAL && !n[0].getType().isBoolean())
  {
    TNode n1 = getEntailedTerm2(n[0]);
    if (!n1.isNull())
    {
      TNode n2 = getEntailedTerm2(n[1]);
      if (!n2.isNull())
      {
        if (n1 == n2)
        {
          d_cacheEntailed[n] = 1;
          return pol;
        }
        else
        {
          Assert(d_qstate.hasTerm(n1));
          Assert(d_qstate.hasTerm(n2));
          if (pol)
          {
            if (d_qstate.areEqual(n1, n2))
            {
              d_cacheEntailed[n] = 1;
              return true;
            }
          }
          else if (d_qstate.areDisequal(n1, n2))
          {
            d_cacheEntailed[n] = -1;
            return true;
          }
          // terms are known, but neither equal nor disequal
          // don't cache?
          return false;
        }
      }
    }
    // at least one term is unknown
    d_cacheEntailed[n] = 0;
  }
  else if (k == NOT)
  {
    return isEntailed2(n[0], !pol);
  }
  else if (k == OR || k == AND)
  {
    bool simPol = (pol && k == OR) || (!pol && k == AND);
    for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      if (isEntailed2(n[i], pol))
      {
        if (simPol)
        {
          d_cacheEntailed[n] = pol ? 1 : -1;
          return true;
        }
      }
      else if (!simPol)
      {
        // value is unknown with this polarity
        return false;
      }
    }
    if (!simPol)
    {
      return true;
    }
  }
  else if (n.getKind() == EQUAL || n.getKind() == ITE)
  {
    for (size_t i = 0; i < 2; i++)
    {
      if (isEntailed2(n[0], i == 0))
      {
        size_t ch = (n.getKind() == EQUAL || i == 0) ? 1 : 2;
        bool reqPol = (n.getKind() == ITE || i == 0) ? pol : !pol;
        return isEntailed2(n[ch], reqPol);
      }
    }
    // the first child is unknown, thus we are unknown
    d_cacheEntailed[n] = 0;
  }
  else if (k == APPLY_UF)
  {
    TNode n1 = getEntailedTerm2(n);
    if (!n1.isNull())
    {
      Assert(d_qstate.hasTerm(n1));
      if (n1 == d_true)
      {
        d_cacheEntailed[n] = 1;
        return pol;
      }
      else if (n1 == d_false)
      {
        d_cacheEntailed[n] = -1;
        return !pol;
      }
      return d_qstate.getRepresentative(n1) == (pol ? d_true : d_false);
    }
    // term is unknown, cache
    d_cacheEntailed[n] = 0;
  }
  else if (k == FORALL && !pol)
  {
    // existentials in rare cases can be entailed
    return isEntailed2(n[1], pol);
  }
  return false;
}

bool EntailmentCheck::isEntailed(TNode n, bool pol)
{
  return isEntailed2(n, pol);
}

bool EntailmentCheck::isEntailed(TNode n,
                                 std::map<TNode, TNode>& subs,
                                 bool subsRep,
                                 bool pol)
{
  
  
  return isEntailed2(n, pol);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
