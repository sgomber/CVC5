/*********************                                                        */
/*! \file gen_ic_pbe.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of gen_ic_pbe
 **/

#include "preprocessing/passes/gen_ic_pbe.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/sygus_sampler.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {

GenIcPbe::GenIcPbe(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "gen-ic-pbe"){};

PreprocessingPassResult GenIcPbe::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  static bool tryThis = true;

  if (!tryThis)
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }
  tryThis = false;

  NodeManager* nm = NodeManager::currentNM();

  std::vector<Node>& asl = assertionsToPreprocess->ref();

  AlwaysAssert(!asl.empty(), "GenIcPbe: no assertions");

  Node icCase = asl[0];
  Trace("gen-ic-pbe")
      << "Generate PBE invertibility condition conjecture for case: " << icCase
      << std::endl;

  AlwaysAssert(icCase.getNumChildren() >= 2,
               "GenIcPbe: bad arity for assertion");

  std::vector<Node> bvars;
  Node funToSynthOp;
  Node funToSynthBvar;

  // match the lists
  std::vector<Node> varList;
  std::vector<Node> funToSynthArgList;

  // convert the child to bound variable form
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(icCase);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      if (cur.getKind() == APPLY_UF)
      {
        AlwaysAssert(funToSynthBvar.isNull(),
                     "GenIcPbe: multiple functions to synthesize");
        funToSynthOp = cur.getOperator();
        std::stringstream ss;
        ss << "x";
        funToSynthBvar = nm->mkBoundVar(ss.str(), cur.getType());
        for (const Node& a : cur)
        {
          funToSynthArgList.push_back(a);
        }
        visited[cur] = funToSynthBvar;
      }
      else if (cur.isVar())
      {
        std::stringstream ss;
        ss << "v" << cur;
        Node bv = nm->mkBoundVar(ss.str(), cur.getType());
        bvars.push_back(bv);
        varList.push_back(cur);
        visited[cur] = bv;
      }
      else
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        unsigned nchild = cur.getNumChildren();
        for (unsigned i = 0; i < nchild; i++)
        {
          visit.push_back(cur[(nchild - 1) - i]);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
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
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(icCase) != visited.end());
  Assert(!visited.find(icCase)->second.isNull());
  Node res = visited[icCase];
  Trace("gen-ic-pbe") << "Bound variable form : " << res << std::endl;
  Trace("gen-ic-pbe-debug") << "...with : " << funToSynthBvar << " " << varList
                            << " " << funToSynthArgList << std::endl;
  // ensure the function type matches the computed type
  AlwaysAssert(!funToSynthBvar.isNull(),
               "GenIcPbe: no functions to synthesize");
  AlwaysAssert(varList.size() == funToSynthArgList.size(),
               "GenIcPbe: function to synthesize has wrong arity");

  for (unsigned i = 0, nvars = varList.size(); i < nvars; i++)
  {
    AlwaysAssert(varList[i] == funToSynthArgList[i],
                 "GenIcPbe: argument list does not match subterms in order");
  }

  TypeNode frange = funToSynthBvar.getType();


  Node xk = nm->mkSkolem("x", frange);

  TNode xt = funToSynthBvar;
  TNode xkt = xk;
  Node resSkolem = res.substitute(xt, xkt);

  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
  std::ostream& out = *nodeManagerOptions.getOut();
  
  std::map< unsigned, std::vector< Node > > completeDom;
  theory::quantifiers::SygusSampler ss;
  theory::quantifiers::TermEnumeration tenum;
  unsigned nsamples = 0;
  if( options::genIcPbeFull() )
  {
    nsamples = bvars.empty() ? 0 : 1;
    for( unsigned i=0, nvars = bvars.size(); i<nvars; i++ )
    {
      TypeNode tn = bvars[i].getType();
      AlwaysAssert(tenum.mayComplete(tn),"GenIcPbe: expecting small finite type when gen-ic-pbe-full");
      unsigned counter = 0;
      Node curre;
      do
      {
        curre = tenum.getEnumerateTerm(tn,counter);
        counter++;
        if( !curre.isNull() )
        {
          completeDom[i].push_back(curre);
        }
      }while(!curre.isNull());
      nsamples = nsamples*completeDom[i].size();
    }
  }
  else
  {
    ss.initialize(frange, bvars, options::sygusSamples());
    nsamples = ss.getNumSamplePoints();
  }

  for (unsigned i = 0; i < nsamples; i++)
  {
    std::vector<Node> samplePt;
    if( options::genIcPbeFull() )
    {
      unsigned ival = i;
      for( unsigned j=0, nvars = bvars.size(); j<nvars; j++ )
      {
        unsigned domSize = completeDom[j].size();
        unsigned currIndex = ival%domSize;
        samplePt.push_back(completeDom[j][currIndex]);
        ival = ival/domSize;
      }
    }
    else
    {
      ss.getSamplePoint(i, samplePt);
    }

    Node resSkolemSubs = resSkolem.substitute(
        bvars.begin(), bvars.end(), samplePt.begin(), samplePt.end());

    Trace("gen-ic-pbe") << i << ": generate I/O spec from " << resSkolemSubs
                        << std::endl;

    SmtEngine smtSamplePt(nm->toExprManager());
    smtSamplePt.setLogic(smt::currentSmtEngine()->getLogicInfo());
    smtSamplePt.assertFormula(resSkolemSubs.toExpr());
    Trace("gen-ic-pbe") << "*** Check sat..." << std::endl;
    Result r = smtSamplePt.checkSat();
    Trace("gen-ic-pbe") << "...result : " << r << std::endl;
    out << "(constraint ";
    if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      out << "(not ";
    }
    out << "(IC ";
    for (const Node& sp : samplePt)
    {
      out << sp << " ";
    }
    if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      out << ")";
    }
    out << "))" << std::endl;
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
