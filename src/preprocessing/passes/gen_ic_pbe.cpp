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
#include "theory/quantifiers/sygus_sampler.h"
#include "theory/quantifiers/term_enumeration.h"
#include "util/random.h"

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
  Notice() << "Generate PBE invertibility condition conjecture for case: "
           << icCase << std::endl;

  AlwaysAssert(icCase.getNumChildren() >= 2,
               "GenIcPbe: bad arity for first assertion");

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

  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
  std::ostream& out = *nodeManagerOptions.getOut();

  std::map<unsigned, std::vector<Node> > completeDom;
  theory::quantifiers::SygusSampler ss;
  theory::quantifiers::TermEnumeration tenum;
  unsigned nsamples = 0;
  bool isFull = (options::genIcPbeFull() || options::testIcFull());
  if (isFull)
  {
    nsamples = bvars.empty() ? 0 : 1;
    for (unsigned i = 0, nvars = bvars.size(); i < nvars; i++)
    {
      TypeNode tn = bvars[i].getType();
      AlwaysAssert(
          tenum.mayComplete(tn),
          "GenIcPbe: expecting small finite type when gen-ic-pbe-full");
      unsigned counter = 0;
      Node curre;
      do
      {
        curre = tenum.getEnumerateTerm(tn, counter);
        Trace("gen-ic-pbe-enum")
            << "Enum " << counter << " " << curre << std::endl;
        counter++;
        if (!curre.isNull())
        {
          completeDom[i].push_back(curre);
        }
      } while (!curre.isNull());
      nsamples = nsamples * completeDom[i].size();
    }
  }
  else
  {
    ss.initialize(frange, bvars, options::sygusSamples());
    nsamples = ss.getNumSamplePoints();
  }

  // the formula we are testing
  Node testFormula;

  std::vector<BitVector> ioString;
  if (options::testIcFull())
  {
    // get the candidate
    AlwaysAssert(asl.size() >= 3,
                 "GenIcPbe: expecting at least 3 assertions to test I/O");
    testFormula = Node::fromExpr(
        smt::currentSmtEngine()->expandDefinitions(asl[1].toExpr()));
    testFormula = testFormula.substitute(
        varList.begin(), varList.end(), bvars.begin(), bvars.end());
    Notice() << "Test candidate IC " << testFormula << "..." << std::endl;

    unsigned assertIndex = 2;
    bool success = true;
    while (success && assertIndex < asl.size())
    {
      success = false;
      Node ioDef = asl[assertIndex];
      if (ioDef.getKind() == EQUAL && ioDef[1].isConst()
          && ioDef[1].getType().isBitVector())
      {
        ioString.push_back(ioDef[1].getConst<BitVector>());
        success = true;
      }
      assertIndex++;
    }
    Notice() << "Testing " << ioString.size() << " inputs..." << std::endl;
  }
  else
  {
    Node xk = nm->mkSkolem("x", frange);
    TNode xt = funToSynthBvar;
    TNode xkt = xk;
    testFormula = res.substitute(xt, xkt);
  }
  Notice() << "Test formula is " << testFormula << std::endl;

  // for test-ic-full, these are the row/column we are looking in
  unsigned ioIndexRow = 0;
  unsigned ioIndexCol = 0;
  unsigned rowWidth = 0;
  if (isFull)
  {
    rowWidth = nsamples / completeDom[0].size();
    if (options::genIcPbeFull())
    {
      out << "(declare-fun io () (Array Int (_ BitVec " << rowWidth << ")))"
          << std::endl;
    }
  }
  unsigned numIncorrect = 0;
  unsigned numIncorrectUndef = 0;
  std::map<bool, unsigned> numIncorrectRes;
  for (unsigned i = 0; i < nsamples; i++)
  {
    unsigned ii = options::testIcRandom() ? Random::getRandom().pick(0,nsamples-1) : i;
    bool printConstraint = false;
    bool printPol = true;
    std::vector<Node> samplePt;
    if (isFull)
    {
      unsigned ival = ii;
      for (unsigned j = 0, nvars = bvars.size(); j < nvars; j++)
      {
        unsigned domSize = completeDom[j].size();
        unsigned currIndex = ival % domSize;
        samplePt.push_back(completeDom[j][currIndex]);
        ival = ival / domSize;
        if (j == 0)
        {
          ioIndexCol = currIndex;
          ioIndexRow = ival;
          if (currIndex == 0)
          {
            if (ival > 0)
            {
              if (options::genIcPbeFull())
              {
                out << "))";
              }
              out << std::endl;
            }
            if (options::genIcPbeFull())
            {
              out << "(assert (= (select io " << ioIndexRow << ") #b";
            }
            else
            {
              out << ioIndexRow << ": ";
            }
          }
        }
      }
    }
    else
    {
      ss.getSamplePoint(i, samplePt);
    }
    Node testFormulaSubs = testFormula.substitute(
        bvars.begin(), bvars.end(), samplePt.begin(), samplePt.end());
    if (options::testIcFull())
    {
      // test the I/O behavior
      //std::cout << ioIndexRow << ", " << ioIndexCol << std::endl;
      bool expect = ioString[ioIndexRow].isBitSet((rowWidth - 1) - ioIndexCol);
      Trace("gen-ic-pbe-debug") << "Check " << testFormulaSubs << std::endl;
      Node resn = theory::Rewriter::rewrite(testFormulaSubs);
      Trace("gen-ic-pbe-debug") << "..got " << resn << std::endl;
      if (!resn.isConst())
      {
        out << "?";
        numIncorrect++;
        numIncorrectUndef++;
      }
      else
      {
        bool result = resn.getConst<bool>();
        if (result != expect)
        {
          if (options::testIcFullGen())
          {
            printConstraint = true;
            printPol = expect;
          }
          else
          {
            out << (result ? "X" : "_");
          }
          numIncorrect++;
          numIncorrectRes[result]++;
        }
        else
        {
          if (!options::testIcFullGen())
          {
            out << (expect ? "1" : "0");
          }
        }
      }
    }
    else
    {
      // compute the I/O behavior: testFormulaSubs has free variable x
      Trace("gen-ic-pbe") << i << ": generate I/O spec from " << testFormulaSubs
                          << std::endl;
      SmtEngine smtSamplePt(nm->toExprManager());
      smtSamplePt.setLogic(smt::currentSmtEngine()->getLogicInfo());
      smtSamplePt.assertFormula(testFormulaSubs.toExpr());
      Trace("gen-ic-pbe") << "*** Check sat..." << std::endl;
      Result r = smtSamplePt.checkSat();
      Trace("gen-ic-pbe") << "...result : " << r << std::endl;
      if (options::genIcPbeFull())
      {
        out << (r.asSatisfiabilityResult().isSat() == Result::UNSAT ? "0"
                                                                    : "1");
      }
      else
      {
        printConstraint = true;
        printPol = (r.asSatisfiabilityResult().isSat() != Result::UNSAT);
      }
    }
    if (printConstraint)
    {
      out << "(constraint ";
      if (!printPol)
      {
        out << "(not ";
      }
      out << "(IC ";
      for (const Node& sp : samplePt)
      {
        out << sp << " ";
      }
      if (!printPol)
      {
        out << ")";
      }
      out << "))" << std::endl;
    }
  }
  if (isFull)
  {
    if (options::genIcPbeFull())
    {
      out << "))";
    }
    out << std::endl;
  }
  if (options::testIcFull())
  {
    out << "       Total #incorrect : " << numIncorrect << std::endl;
    for (std::pair<const bool, unsigned>& ri : numIncorrectRes)
    {
      out << "    Total #incorrect[" << ri.first << "] : " << ri.second
          << std::endl;
    }
    out << "Total #incorrect[undef] : " << numIncorrectUndef << std::endl;
    out << "           Total #tests : " << nsamples << std::endl;
    out << "              % correct : "
        << 1.0 - (double(numIncorrect) / double(nsamples)) << std::endl;
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
