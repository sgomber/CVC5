/*********************                                                        */
/*! \file learned_rewrite.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Caleb Donovick
 ** This file is part of the CVC5 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriting based on learned literals
 **/

#include "preprocessing/passes/learned_rewrite.h"

#include "expr/skolem_manager.h"
#include "expr/term_context_stack.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/arith/arith_msum.h"
#include "theory/rewriter.h"
#include "util/rational.h"

using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace preprocessing {
namespace passes {

LearnedRewrite::LearnedRewrite(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "learned-rewrite")
{
}

PreprocessingPassResult LearnedRewrite::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  arith::BoundInference binfer;
  std::vector<Node> learnedLits = d_preprocContext->getLearnedLiterals();
  std::vector<Node> llrw;
  if (learnedLits.empty())
  {
    Trace("learned-rewrite-ll") << "No learned literals" << std::endl;
  }
  else
  {
    Trace("learned-rewrite-ll") << "Learned literals:" << std::endl;
    for (const Node& l : learnedLits)
    {
      Node e = rewriteLearnedRec(l, binfer, llrw);
      // maybe for bound inference?
      Kind k = e.getKind();
      if (k == EQUAL || k == GEQ)
      {
        binfer.add(e);
        llrw.push_back(e);
      }
      Trace("learned-rewrite-ll") << "- " << e << std::endl;
    }
    Trace("learned-rewrite-ll") << "end" << std::endl;
  }
  size_t size = assertionsToPreprocess->size();
  for (size_t i = 0; i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    Trace("learned-rewrite-assert")
        << "LearnedRewrite: assert: " << prev << std::endl;
    Node e = rewriteLearnedRec(prev, binfer, llrw);
    if (e != prev)
    {
      Trace("learned-rewrite-assert")
          << ".......................: " << e << std::endl;
      assertionsToPreprocess->replace(i, e);
    }
  }
  // add the conjunction of learned literals back to assertions
  if (!llrw.empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    Node llc = nm->mkAnd(llrw);
    Trace("learned-rewrite-assert")
        << "Re-add rewritten learned conjunction: " << llc << std::endl;
    assertionsToPreprocess->push_back(llc);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

Node LearnedRewrite::rewriteLearnedRec(Node n,
                                       arith::BoundInference& binfer,
                                       std::vector<Node>& lems)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
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
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool needsRcons = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        needsRcons = needsRcons || cn != it->second;
        children.push_back(it->second);
      }
      if (needsRcons)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      // rewrite here
      ret = rewriteLearned(ret, binfer, lems);
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node LearnedRewrite::rewriteLearned(Node n,
                                    arith::BoundInference& binfer,
                                    std::vector<Node>& lems)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("learned-rewrite-rr-debug") << "Rewrite " << n << std::endl;
  Node nr = Rewriter::rewrite(n);
  Kind k = nr.getKind();
  if (k == INTS_DIVISION || k == INTS_MODULUS || k == DIVISION)
  {
    // simpler if we know the divisor is non-zero
    Node num = n[0];
    Node den = n[1];
    bool isNonZeroDen = false;
    if (den.isConst())
    {
      isNonZeroDen = (den.getConst<Rational>().sgn() != 0);
    }
    else
    {
      arith::Bounds db = binfer.get(den);
      Trace("learned-rewrite-rr-debug")
          << "Bounds for " << den << " : " << db.lower_value << " "
          << db.upper_value << std::endl;
      if (!db.lower_value.isNull()
          && db.lower_value.getConst<Rational>().sgn() == 1)
      {
        isNonZeroDen = true;
      }
      else if (!db.upper_value.isNull()
               && db.upper_value.getConst<Rational>().sgn() == -1)
      {
        isNonZeroDen = true;
      }
    }
    if (isNonZeroDen)
    {
      Trace("learned-rewrite-rr-debug")
          << "...non-zero denominator" << std::endl;
      Kind nk = k;
      switch (k)
      {
        case INTS_DIVISION: nk = INTS_DIVISION_TOTAL; break;
        case INTS_MODULUS: nk = INTS_MODULUS_TOTAL; break;
        case DIVISION: nk = DIVISION_TOTAL; break;
        default: Assert(false); break;
      }
      std::vector<Node> children;
      children.insert(children.end(), n.begin(), n.end());
      Node ret = nm->mkNode(nk, children);
      nr = returnRewriteLearned(nr, ret, "non_zero_den");
      nr = Rewriter::rewrite(nr);
      k = nr.getKind();
    }
  }
  // constant int mod elimination by bound inference
  if (k == INTS_MODULUS_TOTAL)
  {
    Node num = n[0];
    Node den = n[1];
    arith::Bounds db = binfer.get(den);
    if ((!db.lower_value.isNull()
         && db.lower_value.getConst<Rational>().sgn() == 1)
        || (!db.upper_value.isNull()
            && db.upper_value.getConst<Rational>().sgn() == -1))
    {
      Rational bden = db.lower_value.isNull()
                          ? db.lower_value.getConst<Rational>()
                          : db.upper_value.getConst<Rational>().abs();
      // if 0 <= UB(num) < LB(den) or 0 <= UB(num) < -UB(den)
      arith::Bounds nb = binfer.get(num);
      if (!nb.upper_value.isNull())
      {
        Rational bnum = nb.upper_value.getConst<Rational>();
        if (bnum.sgn() != -1 && bnum < bden)
        {
          nr = returnRewriteLearned(nr, nr[0], "int_mod_range");
        }
      }
      // could also do num + k*den checks
    }
  }
  else if (k == GEQ || (k == EQUAL && nr[0].getType().isReal()))
  {
    std::map<Node, Node> msum;
    if (ArithMSum::getMonomialSumLit(nr, msum))
    {
      Rational lb(0);
      Rational ub(0);
      bool lbSuccess = true;
      bool ubSuccess = true;
      Rational one(1);
      if (Trace.isOn("learned-rewrite-arith-lit"))
      {
        Trace("learned-rewrite-arith-lit")
            << "Arithmetic lit: " << nr << std::endl;
        for (const std::pair<const Node, Node>& m : msum)
        {
          Trace("learned-rewrite-arith-lit")
              << "  " << m.first << ", " << m.second << std::endl;
        }
      }
      for (const std::pair<const Node, Node>& m : msum)
      {
        bool isOneCoeff = m.second.isNull();
        Assert(isOneCoeff || m.second.isConst());
        if (m.first.isNull())
        {
          lb = lb + (isOneCoeff ? one : m.second.getConst<Rational>());
          ub = ub + (isOneCoeff ? one : m.second.getConst<Rational>());
        }
        else
        {
          arith::Bounds b = binfer.get(m.first);
          bool isNeg = !isOneCoeff && m.second.getConst<Rational>().sgn() == -1;
          // flip lower/upper if negative coefficient
          TNode l = isNeg ? b.upper_value : b.lower_value;
          TNode u = isNeg ? b.lower_value : b.upper_value;
          if (lbSuccess && !l.isNull())
          {
            Rational lc = l.getConst<Rational>();
            lb = lb
                 + (isOneCoeff ? lc
                               : Rational(lc * m.second.getConst<Rational>()));
          }
          else
          {
            lbSuccess = false;
          }
          if (ubSuccess && !u.isNull())
          {
            Rational uc = u.getConst<Rational>();
            ub = ub
                 + (isOneCoeff ? uc
                               : Rational(uc * m.second.getConst<Rational>()));
          }
          else
          {
            ubSuccess = false;
          }
          if (!lbSuccess && !ubSuccess)
          {
            break;
          }
        }
      }
      if (lbSuccess)
      {
        if (lb.sgn() == 1)
        {
          // if positive lower bound, then GEQ is true, EQUAL is false
          Node ret = nm->mkConst(k == GEQ);
          nr = returnRewriteLearned(nr, ret, "pred_pos_lb");
          return nr;
        }
        else if (lb.sgn() == 0 && k == GEQ)
        {
          // zero lower bound, GEQ is true
          Node ret = nm->mkConst(true);
          nr = returnRewriteLearned(nr, ret, "pred_zero_lb");
          return nr;
        }
      }
      else if (ubSuccess)
      {
        if (ub.sgn() == -1)
        {
          // if negative upper bound, then GEQ and EQUAL are false
          Node ret = nm->mkConst(false);
          nr = returnRewriteLearned(nr, ret, "pred_neg_ub");
          return nr;
        }
      }
      // inferences based on combining div terms
      Node currDen;
      Node currNum;
      std::vector<Node> sum;
      size_t divCount = 0;
      bool divTotal = true;
      for (const std::pair<const Node, Node>& m : msum)
      {
        if (m.first.isNull())
        {
          sum.push_back(m.second);
          continue;
        }
        Node factor = ArithMSum::mkCoeffTerm(m.second, m.first[0]);
        Kind mk = m.first.getKind();
        if (mk == INTS_DIVISION || mk == INTS_DIVISION_TOTAL)
        {
          divTotal = divTotal && mk == INTS_DIVISION_TOTAL;
          divCount++;
          if (currDen.isNull())
          {
            currNum = factor;
            currDen = m.first[1];
          }
          else
          {
            factor = nm->mkNode(MULT, factor, currDen);
            currNum = nm->mkNode(MULT, currNum, m.first[1]);
            currNum = nm->mkNode(PLUS, currNum, factor);
            currDen = nm->mkNode(MULT, currDen, m.first[1]);
          }
        }
        else
        {
          sum.push_back(factor);
        }
      }
      if (divCount >= 2)
      {
        SkolemManager* sm = nm->getSkolemManager();
        Node r = sm->mkDummySkolem("r", nm->integerType());
        Node d = nm->mkNode(
            divTotal ? INTS_DIVISION_TOTAL : INTS_DIVISION, currNum, currDen);
        sum.push_back(d);
        sum.push_back(r);
        Node bound =
            nm->mkNode(AND,
                       nm->mkNode(LEQ, nm->mkConst(-Rational(divCount - 1)), r),
                       nm->mkNode(LEQ, r, nm->mkConst(Rational(divCount - 1))));
        Node sumn = nm->mkNode(PLUS, sum);
        Node lit = nm->mkNode(k, sumn, nm->mkConst(Rational(0)));
        Node lemma = nm->mkNode(IMPLIES, nr, nm->mkNode(AND, lit, bound));
        Trace("learned-rewrite-div")
            << "Div collect lemma: " << lemma << std::endl;
        lems.push_back(lemma);
      }
    }
  }
  return nr;
}

Node LearnedRewrite::returnRewriteLearned(Node n, Node nr, const char* c)
{
  if (Trace.isOn("learned-rewrite-rr"))
  {
    Trace("learned-rewrite-rr") << "LearnedRewrite::Rewrite: (" << c << ") "
                                << n << " == " << nr << std::endl;
  }
  return nr;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
