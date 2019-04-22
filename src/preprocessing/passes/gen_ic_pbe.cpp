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
  bool isFull =
      (options::genIcFull() || options::testIcFull() || options::genIcImage());
  bool isGen = (options::genIcPbe() || options::genIcFull());
  bool isGenImg = options::genIcImage();
  bool isTest = options::testIcFull();
  Notice() << "Generation of IC utility " << std::endl;
  Notice() << "    Full: " << isFull << std::endl;
  Notice() << "     Gen: " << isGen << std::endl;
  Notice() << "  GenImg: " << isGenImg << std::endl;
  Notice() << "    Test: " << isTest << std::endl;

  NodeManager* nm = NodeManager::currentNM();

  std::vector<Node>& asl = assertionsToPreprocess->ref();

  AlwaysAssert(!asl.empty(), "GenIcPbe: no assertions");

  Node icCase = asl[0];
  // must expand definitions
  icCase =  Node::fromExpr(
        smt::currentSmtEngine()->expandDefinitions(icCase.toExpr()));
  Trace("gen-ic-pbe") << "GenIcPbe::applyInternal: initial assertion: " << icCase << std::endl;
  
  std::vector<Node> bvars;
  if( icCase.getKind()==FORALL )
  {
    for( const Node& v : icCase[0] )
    {
      bvars.push_back(v);
    }
    icCase = icCase[1];
  }
  
  // may have a side condition
  Node sideCondition;
  if (icCase.getKind() == IMPLIES)
  {
    if (options::genIcUseSideCondition())
    {
      sideCondition = icCase[0];
    }
    icCase = icCase[1];
  }

  Notice() << "Generate PBE invertibility condition conjecture for case: "
           << icCase << std::endl;
           
  Node testFormula;
  AlwaysAssert(icCase.getKind()==EQUAL,
                "GenIcPbe: expected an equivalence between IC predicate application and input problem.");
  testFormula = icCase[0];
  AlwaysAssert(testFormula.getType().isBoolean(),
                "GenIcPbe: expected an IC of Boolean type.");
  icCase = icCase[1];
  
  AlwaysAssert( icCase.getKind()==EXISTS,
                 "GenIcPbe: expected an existential." );
  AlwaysAssert(icCase[0].getNumChildren()==1,
                "GenIcPbe: expected an inner existential with only one variable.");
  Node funToSynthBvar = icCase[0][0];
  icCase = icCase[1];
  
  Trace("gen-ic-pbe") << "invertibility condition problem : " << icCase << std::endl;
  Trace("gen-ic-pbe-debug") << "...with variable-to-solve : " << funToSynthBvar << std::endl;
  // ensure the function type matches the computed type
  AlwaysAssert(!funToSynthBvar.isNull(),
               "GenIcPbe: no functions to synthesize");

  TypeNode frange = funToSynthBvar.getType();

  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
  std::ostream& out = *nodeManagerOptions.getOut();

  std::map<unsigned, std::vector<Node> > completeDom;
  theory::quantifiers::SygusSampler samplerPt;
  theory::quantifiers::TermEnumeration tenum;
  unsigned nsamples = 0;
  if (isFull)
  {
    nsamples = 1;
    for (unsigned i = 0, nvars = bvars.size(); i < nvars; i++)
    {
      TypeNode tn = bvars[i].getType();
      bool ret = tenum.getDomain(tn, completeDom[i]);
      AlwaysAssert(
          ret, "GenIcPbe: expecting small finite type when gen-ic-pbe-full");
      nsamples = nsamples * completeDom[i].size();
    }
  }
  else
  {
    samplerPt.initialize(frange, bvars, options::sygusSamples());
    nsamples = samplerPt.getNumSamplePoints();
  }

  // the formula we are testing
  bool isTestSatQuery = false;
  if (!isTest)
  {
    // test the input problem
    if (!options::genIcUseEval())
    {
      // we are doing satisfiability queries, witness x now
      Node xk = nm->mkSkolem("x", frange);
      TNode xt = funToSynthBvar;
      TNode xkt = xk;
      testFormula = icCase.substitute(xt, xkt);
    }
    // To test, it is a satisfiability problem. We either use enumerative
    // evaluation if --gen-ic-use-eval is enabled, or satisfiability checking.
    isTestSatQuery = true;
  }
  Notice() << "Test formula is " << testFormula << std::endl;

  // the ios string
  std::vector<BitVector> ioString;
  if (options::genIcReadIoString())
  {
    AlwaysAssert(
        asl.size() >= 2,
        "GenIcPbe: expecting at least 2 assertions when reading I/O string");
    unsigned assertIndex = 1;
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
      else if (!ioDef.isConst())  // maybe could have extraneous true assertion
      {
        AlwaysAssert(false, "Expecting bit-vector equality for I/O string");
      }
      assertIndex++;
    }
    Notice() << "We have " << ioString.size() << " I/O string inputs..."
             << std::endl;
  }

  // for test-ic-full, these are the row/column we are looking in
  unsigned ioIndexRow = 0;
  unsigned ioIndexCol = 0;
  unsigned rowWidth = 0;
  if (isFull)
  {
    rowWidth = completeDom.empty() ? 1 : completeDom[completeDom.size() - 1].size();
    if (options::genIcFull())
    {
      out << "; Full I/O specification for " << icCase << std::endl;
      out << "(declare-fun io () (Array Int (_ BitVec " << rowWidth << ")))"
          << std::endl;
    }
  }
  std::vector<unsigned> auxIndex;
  for (unsigned i = 0; i < nsamples; i++)
  {
    auxIndex.push_back(i);
  }
  bool useAuxIndex = false;
  if (options::testIcRandom())
  {
    std::shuffle(auxIndex.begin(), auxIndex.end(), Random::getRandom());
    useAuxIndex = true;
  }

  // A list of evaluations for x, to use with --gen-ic-use-eval
  std::vector<Node> xDomUseEval;
  unsigned xdsize = 0;
  if (options::genIcUseEval())
  {
    // Organize an evaluation strategy:
    // start with an interesting set of sample points
    theory::quantifiers::SygusSampler samplerXDom;
    std::vector<Node> xvars;
    std::unordered_set<Node, NodeHashFunction> xvalsUsed;
    xvars.push_back(funToSynthBvar);
    samplerXDom.initialize(frange, xvars, options::sygusSamples());
    for (unsigned i = 0, nxsp = samplerXDom.getNumSamplePoints(); i < nxsp; i++)
    {
      std::vector<Node> xval;
      samplerXDom.getSamplePoint(i, xval);
      Assert(xval.size() == 1);
      Node xv = xval[0];
      xDomUseEval.push_back(xv);
      xvalsUsed.insert(xv);
    }
    // then, take the remainder, in random order
    std::vector<Node> fullDomain;
    bool ret = tenum.getDomain(frange, fullDomain);
    AlwaysAssert(ret);
    std::vector<Node> remainder;
    for (const Node& n : fullDomain)
    {
      if (xvalsUsed.find(n) == xvalsUsed.end())
      {
        remainder.push_back(n);
      }
    }
    std::shuffle(remainder.begin(), remainder.end(), Random::getRandom());
    xDomUseEval.insert(xDomUseEval.end(), remainder.begin(), remainder.end());
    xdsize = xDomUseEval.size();
  }

  if (isGenImg)
  {
    out << "P3 " << rowWidth << " " << (nsamples / rowWidth) << " 256"
        << std::endl;
  }

  unsigned numIncorrect = 0;
  unsigned numIncorrectUndef = 0;
  unsigned numTests = 0;
  unsigned printConstraintCount = 0;
  std::map<bool, unsigned> numIncorrectRes;
  unsigned startIndex = rowWidth * options::genIcR();
  unsigned endIndex = options::genIcEndR()<=0 ? nsamples : rowWidth*options::genIcEndR();
  if( endIndex>nsamples )
  {
    endIndex = nsamples;
  }
  Trace("gen-ic-pbe") << "Row boundaries are " << options::genIcR() << " " << options::genIcEndR() << std::endl;
  for (unsigned i = startIndex; i < endIndex; i++)
  {
    unsigned ii = useAuxIndex ? auxIndex[i] : i;
    bool printConstraint = false;
    bool printPol = true;
    std::vector<Node> samplePt;
    if (isFull)
    {
      unsigned ival = ii;
      unsigned nvars = bvars.empty() ? 1 : bvars.size();
      for (unsigned j = 0; j < nvars; j++)
      {
        unsigned domSize = completeDom.empty() ? 1 : completeDom[j].size();
        unsigned currIndex = ival % domSize;
        if( j<bvars.size() )
        {
          samplePt.push_back(completeDom[j][currIndex]);
        }
        ival = ival / domSize;
        if (j == 0)
        {
          ioIndexCol = currIndex;
          ioIndexRow = ival;
          if (currIndex == 0)
          {
            // considering a new row
            if (isGenImg)
            {
              if (ival > 0)
              {
                out << std::endl;
              }
            }
            else
            {
              if (i > startIndex)
              {
                if (options::genIcFull())
                {
                  out << "))";
                }
                if (!options::testIcGen())
                {
                  out << std::endl;
                }
              }
              if (options::genIcFull())
              {
                out << "(assert (= (select io " << ioIndexRow << ") #b";
              }
              else if (!options::testIcGen())
              {
                out << ioIndexRow << ": ";
              }
            }
          }
        }
      }
    }
    else
    {
      samplerPt.getSamplePoint(i, samplePt);
    }
    Node testFormulaSubs = testFormula.substitute(
        bvars.begin(), bvars.end(), samplePt.begin(), samplePt.end());
    Trace("gen-ic-pbe-debug") << "Check " << testFormulaSubs << std::endl;
    Node resTest = theory::Rewriter::rewrite(testFormulaSubs);
    Trace("gen-ic-pbe-debug") << "..got " << resTest << std::endl;
    bool failSc = false;
    // does it satisfy the side condition?
    if (!sideCondition.isNull())
    {
      Node scResSubs = sideCondition.substitute(
          bvars.begin(), bvars.end(), samplePt.begin(), samplePt.end());
      Trace("gen-ic-pbe-debug")
          << "Check side condition " << scResSubs << std::endl;
      Node resn = theory::Rewriter::rewrite(scResSubs);
      if (resn.isConst() && !resn.getConst<bool>())
      {
        failSc = true;
        Trace("gen-ic-pbe-debug")
            << "Failed side condition: " << samplePt << std::endl;
      }
    }
    if (isGenImg)
    {
      bool res = false;
      bool resValid = true;
      if (isTest)
      {
        if (!resTest.isConst())
        {
          out << "256 0 0 ";
          resValid = false;
        }
        else
        {
          res = resTest.getConst<bool>();
        }
      }
      else
      {
        res = ioString[ioIndexRow].isBitSet((rowWidth - 1) - ioIndexCol);
      }
      if (resValid)
      {
        out << (res ? "256 256 256 " : "0 0 0 ");
      }
    }
    else if (isGen)
    {
      if (!failSc)
      {
        // compute the I/O behavior: testFormulaSubs has free variable x
        Trace("gen-ic-pbe")
            << i << ": generate I/O spec from " << testFormulaSubs << std::endl;
        Result r;
        if (resTest.isConst())
        {
          r = Result(resTest.getConst<bool>() ? Result::SAT : Result::UNSAT);
        }
        else
        {
          AlwaysAssert(isTestSatQuery);
          if (options::genIcUseEval())
          {
            r = Result(Result::UNSAT);
            TNode xt = funToSynthBvar;
            Node testFormulaEval;
            Trace("gen-ic-eval") << "*** Test by evaluation on " << xdsize
                                 << " points..." << std::endl;
            for (unsigned k = 0; k < xdsize; k++)
            {
              TNode xvt = xDomUseEval[k];
              Trace("gen-ic-eval") << "Test " << resTest  << " * { " << xt << " -> " << xvt << " } " << std::endl;
              testFormulaEval = resTest.substitute(xt, xvt);
              testFormulaEval = theory::Rewriter::rewrite(testFormulaEval);
              if (testFormulaEval.isConst())
              {
                if (testFormulaEval.getConst<bool>())
                {
                  r = Result(Result::SAT);
                  Trace("gen-ic-eval")
                      << "...SAT after " << k << " iterations" << std::endl;
                  break;
                }
              }
              else
              {
                // unknown
                r = Result(Result::SAT_UNKNOWN);
                Trace("gen-ic-eval")
                    << "...UNKNOWN after " << k << " iterations" << std::endl;
                break;
              }
            }
            if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
            {
              Trace("gen-ic-eval") << "...UNSAT" << std::endl;
            }
          }
          else
          {
            SmtEngine smtSamplePt(nm->toExprManager());
            smtSamplePt.setLogic(smt::currentSmtEngine()->getLogicInfo());
            smtSamplePt.assertFormula(resTest.toExpr());
            smtSamplePt.setIsInternalSubsolver();
            Trace("gen-ic-pbe") << "*** Check sat..." << std::endl;
            r = smtSamplePt.checkSat();
            Trace("gen-ic-pbe") << "...result : " << r << std::endl;
          }
        }
        if (options::genIcFull())
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
    }
    else if (isTest)
    {
      if (failSc)
      {
        if (!options::testIcGen())
        {
          out << "~";
        }
      }
      else
      {
        numTests++;
        // test the I/O behavior
        Trace("gen-ic-pbe-debug2")
            << "Test point " << ioIndexRow << ", " << ioIndexCol << std::endl;
        Assert(ioIndexRow<ioString.size());
        bool expect =
            ioString[ioIndexRow].isBitSet((rowWidth - 1) - ioIndexCol);
        if (!resTest.isConst())
        {
          if (!options::testIcGen())
          {
            out << "?";
          }
          numIncorrect++;
          numIncorrectUndef++;
        }
        else
        {
          bool result = resTest.getConst<bool>();
          if (result != expect)
          {
            if (options::testIcGen())
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
            if (!options::testIcGen())
            {
              out << (expect ? "1" : "0");
            }
          }
        }
      }
    }
    if (printConstraint)
    {
      out << "(constraint ";
      if (!printPol)
      {
        out << "(not ";
      }
      if( !samplePt.empty() ){
        out << "(";
      }
      out << "IC ";
      for (const Node& sp : samplePt)
      {
        out << sp << " ";
      }
      if( !samplePt.empty() ){
        out << ")";
      }
      if (!printPol)
      {
        out << ")";
      }
      out << ")" << std::endl;
      printConstraintCount++;
      if (printConstraintCount == options::testIcPoints())
      {
        exit(0);
      }
    }
  }
  if (isFull)
  {
    if (options::genIcFull())
    {
      out << "))";
    }
    if (!options::testIcGen())
    {
      out << std::endl;
    }
  }
  if (isTest && !isGen)
  {
    // if we're generating constraints, we may get here if we haven't reached
    // the threshold of number of constraints generated (--test-ic-samples).
    if (!options::testIcGen())
    {
      out << "       Total #incorrect : " << numIncorrect << std::endl;
      for (std::pair<const bool, unsigned>& ri : numIncorrectRes)
      {
        out << "    Total #incorrect[" << ri.first << "] : " << ri.second
            << std::endl;
      }
      if (numIncorrectUndef > 0)
      {
        out << "Total #incorrect[undef] : " << numIncorrectUndef << std::endl;
      }
      out << "           Total #tests : " << numTests << std::endl;
      if (numTests > 0)
      {
        out << "              % correct : "
            << 1.0 - (double(numIncorrect) / double(numTests)) << std::endl;
      }
    }
    if (numIncorrect == 0)
    {
      out << "----> FULLY VERIFIED!!!" << std::endl;
    }
  }
  // FIXME
  exit(0);
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
