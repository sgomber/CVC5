/*********************                                                        */
/*! \file formula_evaluator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of formula evaluator.
 **/

#include "theory/quantifiers/formula_evaluator.h"

#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

FormulaEvaluator::FormulaEvaluator(QuantifiersEngine * qe) : d_qe(qe), d_valuation(qe->getValuation()) {}
  
void FormulaEvaluator::reset() { d_ecache.clear(); }

int FormulaEvaluator::evaluate(Node n, bool cacheUnk)
{
  n = Rewriter::rewrite(n);
  std::unordered_set<Node, NodeHashFunction> ucache;
  return evaluateInternal(n, d_ecache, ucache, cacheUnk);
}
int FormulaEvaluator::evaluateWithAssumptions(Node n,
                                         std::map<Node, int>& assumptions,
                                         bool cacheUnk)
{
  n = Rewriter::rewrite(n);
  std::unordered_set<Node, NodeHashFunction> ucache;
  return evaluateInternal(n, assumptions, ucache, cacheUnk);
}

int FormulaEvaluator::evaluateInternal(
    Node n,
    std::map<Node, int>& cache,
    std::unordered_set<Node, NodeHashFunction>& ucache,
    bool cacheUnk)
{
  std::map<Node, int>::iterator it = cache.find(n);
  if (it != cache.end())
  {
    return it->second;
  }
  std::unordered_set<Node, NodeHashFunction>::iterator itu = ucache.find(n);
  if (itu != ucache.end())
  {
    return 0;
  }
  Kind k = n.getKind();
  if (k == NOT)
  {
    return -evaluateInternal(n[0], cache, ucache, cacheUnk);
  }
  int res = 0;
  if (k == AND || k == OR)
  {
    int expv = (k == OR) ? -1 : 1;
    res = expv;
    for (TNode nc : n)
    {
      int cres = evaluateInternal(nc, cache, ucache, cacheUnk);
      if (cres == -expv)
      {
        res = cres;
        break;
      }
      else if (cres == 0)
      {
        res = 0;
      }
    }
  }
  else if (k == ITE)
  {
    int cres = evaluateInternal(n[0], cache, ucache, cacheUnk);
    if (cres == 0)
    {
      int cres1 = evaluateInternal(n[1], cache, ucache, cacheUnk);
      int cres2 = evaluateInternal(n[2], cache, ucache, cacheUnk);
      res = cres1 == cres2 ? cres1 : 0;
    }
    else
    {
      unsigned checkIndex = cres == 1 ? 1 : 2;
      res = evaluateInternal(n[checkIndex], cache, ucache, cacheUnk);
    }
  }
  else if (k == EQUAL && n[0].getType().isBoolean())
  {
    int cres1 = evaluateInternal(n[0], cache, ucache, cacheUnk);
    if (cres1 != 0)
    {
      int cres2 = evaluateInternal(n[1], cache, ucache, cacheUnk);
      res = cres2 == cres1 ? 1 : (cres2 == 0 ? 0 : -1);
    }
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
  Trace("iex-debug2") << "FormulaEvaluator::evaluateInternal: " << n
                      << " evaluates to " << res << std::endl;
  if (res == 0 && !cacheUnk)
  {
    ucache.insert(n);
  }
  else
  {
    cache[n] = res;
  }
  return res;
}

bool FormulaEvaluator::ensureValue(Node n, bool isTrue, std::map<Node,int>& setAssumps)
{
  std::unordered_set<Node, NodeHashFunction> ucache;
  // if possible, propagate the literal in the clause that must be true
  std::map< bool, std::unordered_set<Node, NodeHashFunction> > visited;
  std::vector<TNode> visit;
  std::vector<bool> visitE;
  TNode cur;
  bool curReq;
  visit.push_back(n);
  visitE.push_back(isTrue);
  do
  {
    cur = visit.back();
    visit.pop_back();
    curReq = visitE.back();
    visitE.pop_back();
    int evCur = evaluateInternal(cur,d_ecache,ucache,false);
    if( evCur!=0 )
    {
      if( (evCur==1)!=curReq )
      {
        // already wrong, we fail
        return false;
      }
      // already correct, nothing to do
    }
    else if (visited[curReq].find(cur) == visited[curReq].end())
    {
      visited[curReq].insert(cur);
      Kind k = cur.getKind();
      if( k==NOT )
      {
        visit.push_back(cur[0]);
        visitE.push_back(!curReq);
      }
      else if (k == AND || k == OR)
      {
        if ((k == AND) == curReq)
        {
          // all are required
          for(TNode cc : cur)
          {
            visit.push_back(cc);
            visitE.push_back(curReq);
          }
        }
        else
        {
          // find one whose value is unknown
          for(TNode cc : cur)
          {
            int cres = evaluateInternal(cc,d_ecache,ucache,false);
            if (cres == 0)
            {
              // if one child is unknown, then we use it
              visit.push_back(cc);
              visitE.push_back(curReq);
              break;
            }
          }
        }
      }
      else if (k == ITE || (k == EQUAL && cur[0].getType().isBoolean()))
      {
        int ev0 = evaluateInternal(cur[0],d_ecache,ucache,false);
        if( ev0!=0 )
        {
          // implies a single requirement
          int index = (k==ITE && ev0==-1) ? 2 : 1;
          bool reqc = (k!=ITE && ev0==-1) ? !curReq : curReq;
          visit.push_back(cur[index]);
          visitE.push_back(reqc);
        }
        else if( k==ITE )
        {
          // (ite ? ev1 ev2)
          // find a branch that does not have a wrong value
          int processIndex = -1;
          bool processIndexUnk = false;
          for( unsigned i=1; i<=2; i++ )
          {
            int evi = evaluateInternal(cur[i],d_ecache,ucache,false);
            if( (evi==1)==curReq )
            {
              processIndex = i;
              processIndexUnk = false;
              break;
            }
            else if( evi==0 )
            {
              processIndex = i;
              processIndexUnk = true;
            }
          }
          visit.push_back(cur[0]);
          visitE.push_back(processIndex==1);
          if( processIndexUnk )
          {
            visit.push_back(cur[processIndex]);
            visitE.push_back(curReq);
          }
        }
        else
        {
          // ? = ev1
          int ev1 = evaluateInternal(cur[1],d_ecache,ucache,false);
          if( ev1==0 )
          {
            // make both true
            visit.push_back(cur[0]);
            visitE.push_back(true);
            visit.push_back(cur[1]);
            visitE.push_back(true);
          }
          else
          {
            // make match
            visit.push_back(cur[0]);
            visitE.push_back((ev1==1)==curReq);
          }
        }
      }
      else
      {
        int value = curReq ? 1 : -1;
        setAssumps[cur] = value;
        // update it permanently in the cache
        d_ecache[cur] = value;
      }
    }
  } while (!visit.empty());
  
  
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
