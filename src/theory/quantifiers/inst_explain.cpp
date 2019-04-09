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

void IeEvaluator::reset() { d_ecache.clear(); }

int IeEvaluator::evaluate(Node n)
{
  n = Rewriter::rewrite(n);
  return evaluateInternal(n, d_ecache);
}
int IeEvaluator::evaluateWithAssumptions(Node n,
                                         std::map<Node, int>& assumptions)
{
  n = Rewriter::rewrite(n);
  return evaluateInternal(n, assumptions);
}

int IeEvaluator::evaluateInternal(Node n, std::map<Node, int>& cache)
{
  std::map<Node, int>::iterator it = cache.find(n);
  if (it != cache.end())
  {
    return it->second;
  }
  Kind k = n.getKind();
  if (k == NOT)
  {
    return -evaluateInternal(n[0], cache);
  }
  int res = 0;
  if (k == AND || k == OR)
  {
    int expv = (k == OR) ? 1 : -1;
    for (TNode nc : n)
    {
      int cres = evaluateInternal(nc, cache);
      if (cres == expv || cres == 0)
      {
        cache[n] = expv;
        return expv;
      }
    }
    res = -expv;
  }
  else if (k == ITE)
  {
    unsigned checkIndex = evaluateInternal(n[0], cache) ? 1 : 2;
    res = evaluateInternal(n[checkIndex], cache);
  }
  else if (k == EQUAL && n[0].getType().isBoolean())
  {
    res = evaluateInternal(n[0], cache) == evaluateInternal(n[1], cache);
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
  cache[n] = res;
  return res;
}

void InstExplainLit::initialize(Node lit) { d_this = lit; }
void InstExplainLit::reset()
{
  d_curr_insts.clear();
  d_curr_olits.clear();
}
void InstExplainLit::addInstExplanation(Node inst)
{
  // Add to instantiations if not already there.
  if (std::find(d_insts.begin(), d_insts.end(), inst) == d_insts.end())
  {
    d_insts.push_back(inst);
  }
}

void InstExplainLit::setPropagating(Node inst, Node olit)
{
  Assert(std::find(d_insts.begin(), d_insts.end(), inst) != d_insts.end());
  d_curr_insts.push_back(inst);
  d_curr_olits.push_back(olit);
}

void InstExplainInst::initialize(Node inst,
                                 Node body,
                                 Node q,
                                 const std::vector<Node>& ts)
{
  Assert(!q.isNull());
  Assert(q.getKind() == FORALL);
  Assert(ts.size() == q[0].getNumChildren());
  Assert(d_terms.empty());
  d_body = body;
  // notice that inst may be null (in the case we haven't explicitly constructed
  // the instantiation)
  d_this = inst;
  d_quant = q;
  d_terms.insert(d_terms.end(), ts.begin(), ts.end());
}

void InstExplainInst::propagate(IeEvaluator& v,
                                std::vector<Node>& lits,
                                std::vector<Node>& olits)
{
  propagateInternal(d_body, d_quant[1], v, lits, olits);
}

bool InstExplainInst::justify(IeEvaluator& v,
                              Node lit,
                              Node olit,
                              std::vector<Node>& lits,
                              std::vector<Node>& olits)
{
  std::map<Node, std::map<bool, bool> > cache;
  // we assume that lit is false
  Assert(lit == Rewriter::rewrite(lit));
  std::map<Node, int> assumptions;
  assumptions[lit] = -1;
  // the quantified formula must hold in the current context. If it does, it
  // is always a part of the explanation below.
  if (v.evaluate(d_quant) == 1)
  {
    // now, explain why the remainder was false
    if (justifyInternal(d_body,
                        d_quant[1],
                        false,
                        olit,
                        v,
                        assumptions,
                        cache,
                        lits,
                        olits))
    {
      // the quantified formula is always a part of the explanation
      lits.push_back(d_quant);
      olits.push_back(d_quant);
      return true;
    }
  }
  return false;
}

void InstExplainInst::propagateInternal(Node n,
                                        Node on,
                                        IeEvaluator& v,
                                        std::vector<Node>& lits,
                                        std::vector<Node>& olits)
{
  // if possible, propagate the literal in the clause that must be true
  std::unordered_set<Node, NodeHashFunction> visited;
  std::vector<Node> visit;
  std::vector<Node> visito;
  Node cur;
  Node curo;
  visit.push_back(n);
  visito.push_back(on);
  do
  {
    cur = visit.back();
    visit.pop_back();
    curo = visito.back();
    visito.pop_back();
    // cur should hold in the current context
    Assert(v.evaluate(cur) == 1);
    // only safe to cache on the original, not the instance
    if (visited.find(curo) == visited.end())
    {
      visited.insert(curo);
      Assert(cur.getKind() == curo.getKind());
      bool pol = cur.getKind() != NOT;
      Node atom = pol ? cur : cur[0];
      Node atomo = pol ? curo : curo[0];
      Assert(atom.getKind() == atomo.getKind());
      Kind k = atom.getKind();
      if (k == AND || k == OR)
      {
        Assert(atom.getNumChildren() == atomo.getNumChildren());
        if ((k == AND) == pol)
        {
          // they all propagate
          for (unsigned i = 0, nchild = atom.getNumChildren(); i < nchild; i++)
          {
            visit.push_back(pol ? atom[i] : atom[i].negate());
            visito.push_back(pol ? atomo[i] : atomo[i].negate());
          }
        }
        else
        {
          // propagate one if all others are false
          Node trueLit;
          Node trueLito;
          for (unsigned i = 0, nchild = atom.getNumChildren(); i < nchild; i++)
          {
            int cres = v.evaluate(atom[i]);
            if (cres == 0)
            {
              // if one child is unknown, then there are no propagations
              trueLit = Node::null();
              trueLito = Node::null();
              break;
            }
            else if ((cres > 0) == pol)
            {
              if (trueLit.isNull())
              {
                trueLit = atom[i];
                trueLito = atomo[i];
              }
              else
              {
                // two literals are true, no propagations
                trueLit = Node::null();
                trueLito = Node::null();
                break;
              }
            }
          }
          if (!trueLit.isNull())
          {
            visit.push_back(pol ? trueLit : trueLit.negate());
            visito.push_back(pol ? trueLito : trueLito.negate());
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
        if (cbres != 0)
        {
          for (unsigned i = 0; i < 2; i++)
          {
            int cres = v.evaluate(atom[i + 1]);
            if (cres == 0)
            {
              // if one child is unknown, there are no propagations
              break;
            }
            else if ((cres > 0) != pol)
            {
              visit.push_back(pol ? atom[2 - i] : atom[2 - i].negate());
              visito.push_back(pol ? atomo[2 - i] : atomo[2 - i].negate());
              visit.push_back(i == 0 ? atom[0].negate() : atom[0]);
              visito.push_back(i == 0 ? atomo[0].negate() : atomo[0]);
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
        Assert(cres != 0);
        visit.push_back(cres > 0 ? atom[0] : atom[0].negate());
        visito.push_back(cres > 0 ? atomo[0] : atomo[0].negate());
        visit.push_back((cres > 0) == pol ? atom[1] : atom[1].negate());
        visito.push_back((cres > 0) == pol ? atomo[1] : atomo[1].negate());
      }
      else
      {
        // propagates, now go ahead and rewrite cur
        lits.push_back(Rewriter::rewrite(cur));
        olits.push_back(curo);
      }
    }
  } while (!visit.empty());
}

bool InstExplainInst::justifyInternal(
    TNode n,
    TNode on,
    bool pol,
    Node olitProp,
    IeEvaluator& v,
    std::map<Node, int>& assumptions,
    std::map<Node, std::map<bool, bool> >& cache,
    std::vector<Node>& lits,
    std::vector<Node>& olits)
{
  Trace("iex-debug") << "justifyInternal: " << std::endl;
  Trace("iex-debug") << "  " << n << std::endl;
  Trace("iex-debug") << "  " << on << std::endl;
  if (on == olitProp)
  {
    return true;
  }
  // only safe to cache wrt on
  std::map<bool, bool>::iterator it = cache[on].find(pol);
  if (it != cache[on].end())
  {
    return it->second;
  }
  // must justify why n evaluates to pol
  Assert(n.getKind() == on.getKind());
  Assert(v.evaluateWithAssumptions(n, assumptions) == (pol ? 1 : -1));
  if (n.getKind() == NOT)
  {
    return justifyInternal(
        n[0], on[0], !pol, olitProp, v, assumptions, cache, lits, olits);
  }
  cache[on][pol] = true;
  Kind k = n.getKind();
  if (k == AND || k == OR)
  {
    Assert(n.getNumChildren() == on.getNumChildren());
    if ((k == AND) == pol)
    {
      // must explain all of them
      for (unsigned i = 0, nchild = n.getNumChildren(); i < nchild; i++)
      {
        if (!justifyInternal(
                n[i], on[i], pol, olitProp, v, assumptions, cache, lits, olits))
        {
          cache[on][pol] = false;
          return false;
        }
      }
    }
    // must explain one that evaluates to true
    for (unsigned i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      if (v.evaluateWithAssumptions(n[i], assumptions) == (pol ? 1 : -1))
      {
        if (justifyInternal(
                n[i], on[i], pol, olitProp, v, assumptions, cache, lits, olits))
        {
          return true;
        }
      }
    }
    cache[on][pol] = false;
    return false;
  }
  else if (k == ITE)
  {
    int cbres = v.evaluateWithAssumptions(n[0], assumptions);
    if (cbres == 0)
    {
      // branch is unknown, must do both
      if (!justifyInternal(
              n[1], on[1], pol, olitProp, v, assumptions, cache, lits, olits)
          || !justifyInternal(n[2],
                              on[2],
                              pol,
                              olitProp,
                              v,
                              assumptions,
                              cache,
                              lits,
                              olits))
      {
        cache[on][pol] = false;
        return false;
      }
    }
    else
    {
      // branch is known, do relevant child
      unsigned checkIndex = cbres > 0 ? 1 : 2;
      if (!justifyInternal(n[0],
                           on[0],
                           cbres == 1,
                           olitProp,
                           v,
                           assumptions,
                           cache,
                           lits,
                           olits)
          || !justifyInternal(n[checkIndex],
                              on[checkIndex],
                              pol,
                              olitProp,
                              v,
                              assumptions,
                              cache,
                              lits,
                              olits))
      {
        cache[on][pol] = false;
        return false;
      }
    }
  }
  else if (k == EQUAL && n[0].getType().isBoolean())
  {
    int cbres = v.evaluateWithAssumptions(n[0], assumptions);
    if (cbres == 0)
    {
      cache[on][pol] = false;
      return false;
    }
    // must always do both
    if (!justifyInternal(n[0],
                         on[0],
                         cbres == 1,
                         olitProp,
                         v,
                         assumptions,
                         cache,
                         lits,
                         olits)
        || !justifyInternal(n[1],
                            on[1],
                            cbres == 1,
                            olitProp,
                            v,
                            assumptions,
                            cache,
                            lits,
                            olits))
    {
      cache[on][pol] = false;
      return false;
    }
  }
  else
  {
    // must get rewritten version of nn
    Node nn = n;
    nn = Rewriter::rewrite(pol ? nn : nn.negate());
    Node onn = on;
    onn = pol ? onn : onn.negate();
    lits.push_back(nn);
    olits.push_back(onn);
  }
  return true;
}

Node InstExplainInst::getQuantifiedFormula() const { return d_quant; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
