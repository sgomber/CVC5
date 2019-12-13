/*********************                                                        */
/*! \file datatypes_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of rewriter for the theory of (co)inductive datatypes.
 **
 ** Implementation of rewriter for the theory of (co)inductive datatypes.
 **/

#include "theory/datatypes/datatypes_rewriter.h"

#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "expr/sygus_datatype.h"
#include "options/datatypes_options.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/datatypes/codatatype_normalize.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace datatypes {

RewriteResponse DatatypesRewriter::postRewrite(TNode in)
{
  Trace("datatypes-rewrite-debug") << "post-rewriting " << in << std::endl;
  Kind k = in.getKind();
  NodeManager* nm = NodeManager::currentNM();
  if (k == kind::APPLY_CONSTRUCTOR)
  {
    return rewriteConstructor(in);
  }
  else if (k == kind::APPLY_SELECTOR_TOTAL || k == kind::APPLY_SELECTOR)
  {
    return rewriteSelector(in);
  }
  else if (k == kind::APPLY_TESTER)
  {
    return rewriteTester(in);
  }
  else if (k == kind::DT_SIZE)
  {
    if (in[0].getKind() == kind::APPLY_CONSTRUCTOR)
    {
      std::vector<Node> children;
      for (unsigned i = 0, size = in [0].getNumChildren(); i < size; i++)
      {
        if (in[0][i].getType().isDatatype())
        {
          children.push_back(nm->mkNode(kind::DT_SIZE, in[0][i]));
        }
      }
      TNode constructor = in[0].getOperator();
      size_t constructorIndex = utils::indexOf(constructor);
      const DType& dt = utils::datatypeOf(constructor);
      const DTypeConstructor& c = dt[constructorIndex];
      unsigned weight = c.getWeight();
      children.push_back(nm->mkConst(Rational(weight)));
      Node res =
          children.size() == 1 ? children[0] : nm->mkNode(kind::PLUS, children);
      Trace("datatypes-rewrite")
          << "DatatypesRewriter::postRewrite: rewrite size " << in << " to "
          << res << std::endl;
      return RewriteResponse(REWRITE_AGAIN_FULL, res);
    }
  }
  else if (k == kind::DT_HEIGHT_BOUND)
  {
    if (in[0].getKind() == kind::APPLY_CONSTRUCTOR)
    {
      std::vector<Node> children;
      Node res;
      Rational r = in[1].getConst<Rational>();
      Rational rmo = Rational(r - Rational(1));
      for (unsigned i = 0, size = in [0].getNumChildren(); i < size; i++)
      {
        if (in[0][i].getType().isDatatype())
        {
          if (r.isZero())
          {
            res = nm->mkConst(false);
            break;
          }
          children.push_back(
              nm->mkNode(kind::DT_HEIGHT_BOUND, in[0][i], nm->mkConst(rmo)));
        }
      }
      if (res.isNull())
      {
        res = children.size() == 0
                  ? nm->mkConst(true)
                  : (children.size() == 1 ? children[0]
                                          : nm->mkNode(kind::AND, children));
      }
      Trace("datatypes-rewrite")
          << "DatatypesRewriter::postRewrite: rewrite height " << in << " to "
          << res << std::endl;
      return RewriteResponse(REWRITE_AGAIN_FULL, res);
    }
  }
  else if (k == kind::DT_SIZE_BOUND)
  {
    if (in[0].isConst())
    {
      Node res = nm->mkNode(kind::LEQ, nm->mkNode(kind::DT_SIZE, in[0]), in[1]);
      return RewriteResponse(REWRITE_AGAIN_FULL, res);
    }
  }
  else if (k == DT_SYGUS_EVAL)
  {
    // sygus evaluation function
    Node ev = in[0];
    if (ev.getKind() == APPLY_CONSTRUCTOR)
    {
      Trace("dt-sygus-util") << "Rewrite " << in << " by unfolding...\n";
      Trace("dt-sygus-util") << "Type is " << in.getType() << std::endl;
      std::vector<Node> args;
      for (unsigned j = 1, nchild = in.getNumChildren(); j < nchild; j++)
      {
        args.push_back(in[j]);
      }
      Node ret = utils::sygusToBuiltinEval(ev, args);
      Trace("dt-sygus-util") << "...got " << ret << "\n";
      Trace("dt-sygus-util") << "Type is " << ret.getType() << std::endl;
      Assert(in.getType().isComparableTo(ret.getType()));
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
  }
  else if (k == MATCH)
  {
    Trace("dt-rewrite-match") << "Rewrite match: " << in << std::endl;
    Node h = in[0];
    std::vector<Node> cases;
    std::vector<Node> rets;
    TypeNode t = h.getType();
    const DType& dt = t.getDType();
    for (size_t k = 1, nchild = in.getNumChildren(); k < nchild; k++)
    {
      Node c = in[k];
      Node cons;
      Kind ck = c.getKind();
      if (ck == MATCH_CASE)
      {
        Assert(c[0].getKind() == APPLY_CONSTRUCTOR);
        cons = c[0].getOperator();
      }
      else if (ck == MATCH_BIND_CASE)
      {
        if (c[1].getKind() == APPLY_CONSTRUCTOR)
        {
          cons = c[1].getOperator();
        }
      }
      else
      {
        AlwaysAssert(false);
      }
      size_t cindex = 0;
      // cons is null in the default case
      if (!cons.isNull())
      {
        cindex = utils::indexOf(cons);
      }
      Node body;
      if (ck == MATCH_CASE)
      {
        body = c[1];
      }
      else if (ck == MATCH_BIND_CASE)
      {
        std::vector<Node> vars;
        std::vector<Node> subs;
        if (cons.isNull())
        {
          Assert(c[1].getKind() == BOUND_VARIABLE);
          vars.push_back(c[1]);
          subs.push_back(h);
        }
        else
        {
          for (size_t i = 0, vsize = c[0].getNumChildren(); i < vsize; i++)
          {
            vars.push_back(c[0][i]);
            Node sc = nm->mkNode(
                APPLY_SELECTOR_TOTAL, dt[cindex].getSelectorInternal(t, i), h);
            subs.push_back(sc);
          }
        }
        body =
            c[2].substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      }
      if (!cons.isNull())
      {
        cases.push_back(utils::mkTester(h, cindex, dt));
      }
      else
      {
        // variables have no constraints
        cases.push_back(nm->mkConst(true));
      }
      rets.push_back(body);
    }
    Assert(!cases.empty());
    // now make the ITE
    std::reverse(cases.begin(), cases.end());
    std::reverse(rets.begin(), rets.end());
    Node ret = rets[0];
    AlwaysAssert(cases[0].isConst() || cases.size() == dt.getNumConstructors());
    for (unsigned i = 1, ncases = cases.size(); i < ncases; i++)
    {
      ret = nm->mkNode(ITE, cases[i], rets[i], ret);
    }
    Trace("dt-rewrite-match")
        << "Rewrite match: " << in << " ... " << ret << std::endl;
    return RewriteResponse(REWRITE_AGAIN_FULL, ret);
  }

  if (k == kind::EQUAL)
  {
    if (in[0] == in[1])
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
    }
    std::vector<Node> rew;
    if (utils::checkClash(in[0], in[1], rew))
    {
      Trace("datatypes-rewrite")
          << "Rewrite clashing equality " << in << " to false" << std::endl;
      return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
      //}else if( rew.size()==1 && rew[0]!=in ){
      //  Trace("datatypes-rewrite") << "Rewrite equality " << in << " to " <<
      //  rew[0] << std::endl;
      //  return RewriteResponse(REWRITE_AGAIN_FULL, rew[0] );
    }
    else if (in[1] < in[0])
    {
      Node ins = nm->mkNode(in.getKind(), in[1], in[0]);
      Trace("datatypes-rewrite")
          << "Swap equality " << in << " to " << ins << std::endl;
      return RewriteResponse(REWRITE_DONE, ins);
    }
    Trace("datatypes-rewrite-debug")
        << "Did not rewrite equality " << in << " " << in[0].getKind() << " "
        << in[1].getKind() << std::endl;
  }

  return RewriteResponse(REWRITE_DONE, in);
}

RewriteResponse DatatypesRewriter::preRewrite(TNode in)
{
  Trace("datatypes-rewrite-debug") << "pre-rewriting " << in << std::endl;
  // must prewrite to apply type ascriptions since rewriting does not preserve
  // types
  if (in.getKind() == kind::APPLY_CONSTRUCTOR)
  {
    TypeNode tn = in.getType();

    // check for parametric datatype constructors
    // to ensure a normal form, all parameteric datatype constructors must have
    // a type ascription
    if (tn.isParametricDatatype())
    {
      if (in.getOperator().getKind() != kind::APPLY_TYPE_ASCRIPTION)
      {
        Trace("datatypes-rewrite-debug")
            << "Ascribing type to parametric datatype constructor " << in
            << std::endl;
        Node op = in.getOperator();
        // get the constructor object
        const DTypeConstructor& dtc = utils::datatypeOf(op)[utils::indexOf(op)];
        // create ascribed constructor type
        Node tc = NodeManager::currentNM()->mkConst(
            AscriptionType(dtc.getSpecializedConstructorType(tn).toType()));
        Node op_new = NodeManager::currentNM()->mkNode(
            kind::APPLY_TYPE_ASCRIPTION, tc, op);
        // make new node
        std::vector<Node> children;
        children.push_back(op_new);
        children.insert(children.end(), in.begin(), in.end());
        Node inr =
            NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, children);
        Trace("datatypes-rewrite-debug") << "Created " << inr << std::endl;
        return RewriteResponse(REWRITE_DONE, inr);
      }
    }
  }
  return RewriteResponse(REWRITE_DONE, in);
}

RewriteResponse DatatypesRewriter::rewriteConstructor(TNode in)
{
  if (in.isConst())
  {
    Trace("datatypes-rewrite-debug") << "Normalizing constant " << in
                                     << std::endl;
    Node inn = CoDatatypeNormalize::normalizeConstant(in);
    // constant may be a subterm of another constant, so cannot assume that this
    // will succeed for codatatypes
    // Assert( !inn.isNull() );
    if (!inn.isNull() && inn != in)
    {
      Trace("datatypes-rewrite") << "Normalized constant " << in << " -> "
                                 << inn << std::endl;
      return RewriteResponse(REWRITE_DONE, inn);
    }
    return RewriteResponse(REWRITE_DONE, in);
  }
  return RewriteResponse(REWRITE_DONE, in);
}

RewriteResponse DatatypesRewriter::rewriteSelector(TNode in)
{
  Kind k = in.getKind();
  if (in[0].getKind() == kind::APPLY_CONSTRUCTOR)
  {
    // Have to be careful not to rewrite well-typed expressions
    // where the selector doesn't match the constructor,
    // e.g. "pred(zero)".
    TypeNode tn = in.getType();
    TypeNode argType = in[0].getType();
    Node selector = in.getOperator();
    TNode constructor = in[0].getOperator();
    size_t constructorIndex = utils::indexOf(constructor);
    const DType& dt = utils::datatypeOf(selector);
    const DTypeConstructor& c = dt[constructorIndex];
    Trace("datatypes-rewrite-debug") << "Rewriting collapsable selector : "
                                     << in;
    Trace("datatypes-rewrite-debug") << ", cindex = " << constructorIndex
                                     << ", selector is " << selector
                                     << std::endl;
    // The argument that the selector extracts, or -1 if the selector is
    // is wrongly applied.
    int selectorIndex = -1;
    if (k == kind::APPLY_SELECTOR_TOTAL)
    {
      // The argument index of internal selectors is obtained by
      // getSelectorIndexInternal.
      selectorIndex = c.getSelectorIndexInternal(selector);
    }
    else
    {
      // The argument index of external selectors (applications of
      // APPLY_SELECTOR) is given by an attribute and obtained via indexOf below
      // The argument is only valid if it is the proper constructor.
      selectorIndex = utils::indexOf(selector);
      if (selectorIndex < 0
          || selectorIndex >= static_cast<int>(c.getNumArgs()))
      {
        selectorIndex = -1;
      }
      else if (c[selectorIndex].getSelector() != selector)
      {
        selectorIndex = -1;
      }
    }
    Trace("datatypes-rewrite-debug") << "Internal selector index is "
                                     << selectorIndex << std::endl;
    if (selectorIndex >= 0)
    {
      Assert(selectorIndex < (int)c.getNumArgs());
      if (dt.isCodatatype() && in[0][selectorIndex].isConst())
      {
        // must replace all debruijn indices with self
        Node sub = replaceDebruijn(in[0][selectorIndex], in[0], argType, 0);
        Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                   << "Rewrite trivial codatatype selector "
                                   << in << " to " << sub << std::endl;
        if (sub != in)
        {
          return RewriteResponse(REWRITE_AGAIN_FULL, sub);
        }
      }
      else
      {
        Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                   << "Rewrite trivial selector " << in
                                   << std::endl;
        return RewriteResponse(REWRITE_DONE, in[0][selectorIndex]);
      }
    }
    else if (k == kind::APPLY_SELECTOR_TOTAL)
    {
      Node gt;
      bool useTe = true;
      // if( !tn.isSort() ){
      //  useTe = false;
      //}
      if (tn.isDatatype())
      {
        const DType& dta = tn.getDType();
        useTe = !dta.isCodatatype();
      }
      if (useTe)
      {
        TypeEnumerator te(tn);
        gt = *te;
      }
      else
      {
        gt = tn.mkGroundTerm();
      }
      if (!gt.isNull())
      {
        // Assert( gtt.isDatatype() || gtt.isParametricDatatype() );
        if (tn.isDatatype() && !tn.isInstantiatedDatatype())
        {
          gt = NodeManager::currentNM()->mkNode(
              kind::APPLY_TYPE_ASCRIPTION,
              NodeManager::currentNM()->mkConst(AscriptionType(tn.toType())),
              gt);
        }
        Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                   << "Rewrite trivial selector " << in
                                   << " to distinguished ground term " << gt
                                   << std::endl;
        return RewriteResponse(REWRITE_DONE, gt);
      }
    }
  }
  return RewriteResponse(REWRITE_DONE, in);
}

RewriteResponse DatatypesRewriter::rewriteTester(TNode in)
{
  if (in[0].getKind() == kind::APPLY_CONSTRUCTOR)
  {
    bool result =
        utils::indexOf(in.getOperator()) == utils::indexOf(in[0].getOperator());
    Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                               << "Rewrite trivial tester " << in << " "
                               << result << std::endl;
    return RewriteResponse(REWRITE_DONE,
                           NodeManager::currentNM()->mkConst(result));
  }
  const DType& dt = in[0].getType().getDType();
  if (dt.getNumConstructors() == 1 && !dt.isSygus())
  {
    // only one constructor, so it must be
    Trace("datatypes-rewrite")
        << "DatatypesRewriter::postRewrite: "
        << "only one ctor for " << dt.getName() << " and that is "
        << dt[0].getName() << std::endl;
    return RewriteResponse(REWRITE_DONE,
                           NodeManager::currentNM()->mkConst(true));
  }
  // could try dt.getNumConstructors()==2 && indexOf(in.getOperator())==1 ?
  return RewriteResponse(REWRITE_DONE, in);
}

} /* CVC4::theory::datatypes namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
