/*********************                                                        */
/*! \file anonymize_strings.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The rewrite preprocessing pass
 **
 ** Calls the rewriter on every assertion
 **/

#include "preprocessing/passes/anonymize_strings.h"

#include <unordered_map>
#include <unordered_set>
#include "util/random.h"

#include "options/strings_options.h"
#include "preprocessing/passes/anon_str_graph.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

namespace {

Node randomLiteral(unsigned base, unsigned l)
{
  std::vector<unsigned> vec;
  for (unsigned i = 0; i < l; i++)
  {
    // add a digit
    unsigned digit = Random::getRandom().pick(0, base - 1);
    vec.push_back(digit);
  }
  return NodeManager::currentNM()->mkConst(String(vec));
}

Node approxSolveNode(Node l,
                     CtnNode& cl,
                     const std::vector<Node>& fitSet,
                     unsigned fitSetLenSum)
{
  Assert(l.isConst());
  // number of digits to include
  unsigned base = 36;
  unsigned len = l.getConst<String>().size();
  // try to pack the fit set into the string's length
  if (fitSet.empty())
  {
    // base case, it is a random value
    return randomLiteral(base, len);
  }
  std::vector<Node> fsCurr = fitSet;
  NodeManager* nm = NodeManager::currentNM();
  if (fitSetLenSum > len)
  {
    // try to fit based on overlaps TODO
    Trace("str-anon-graph") << "********* Need fit for " << l << " ("
                            << fitSetLenSum << "/" << len << ")" << std::endl;
    // first, randomize
    std::vector<Node> fitSetM = fsCurr;
    fsCurr.clear();
    std::shuffle(fitSetM.begin(), fitSetM.end(), Random::getRandom());
    // now, compute overlaps
    std::unordered_set<unsigned> rm;
    for (const Node& f : fitSetM)
    {
      // find the best index to merge
      std::size_t maxOverlap = 0;
      bool maxOverlapRev = false;
      unsigned maxOverlapIndex = 0;
      // only if we still need to
      if (fitSetLenSum > len)
      {
        String fs = f.getConst<String>();
        for (unsigned j = 0, fsize = fsCurr.size(); j < fsize; j++)
        {
          Node fo = fsCurr[j];
          Trace("str-anon-graph-debug")
              << "Overlaps of " << f << " " << fo << "..." << std::endl;
          String fos = fo.getConst<String>();
          for (unsigned d = 0; d < 2; d++)
          {
            std::size_t oVal = d == 0 ? fos.overlap(fs) : fos.roverlap(fs);
            Trace("str-anon-graph-debug")
                << "  overlap " << d << " is " << oVal << std::endl;
            // for randomization, do not always choose the maximal
            if (oVal > maxOverlap
                && (maxOverlap == 0 || Random::getRandom().pickWithProb(0.75)))
            {
              maxOverlap = oVal;
              maxOverlapRev = (d == 1);
              maxOverlapIndex = j;
              Trace("str-anon-graph-debug") << "Max overlap " << maxOverlap
                                            << " at index " << j << std::endl;
            }
          }
        }
      }
      Trace("str-anon-graph-debug")
          << "Finish, max overlap is " << maxOverlap << std::endl;
      if (maxOverlap > 0)
      {
        fitSetLenSum -= maxOverlap;
        // merge the two strings
        std::vector<unsigned> mVec;
        for (unsigned m = 0; m < 2; m++)
        {
          Node sm = (m == 0) == maxOverlapRev ? f : fsCurr[maxOverlapIndex];
          const std::vector<unsigned>& smVec = sm.getConst<String>().getVec();
          // compute the size to keep
          Assert(maxOverlap < smVec.size());
          unsigned nmsSize = smVec.size() - maxOverlap;
          if (m == 0)
          {
            mVec.insert(mVec.end(), smVec.begin(), smVec.begin() + nmsSize);
          }
          else
          {
            mVec.insert(mVec.end(), smVec.begin() + nmsSize, smVec.end());
          }
        }
        Node merged = nm->mkConst(String(mVec));
        Trace("str-anon-graph")
            << "*** merge " << f << " and " << fsCurr[maxOverlapIndex] << " by "
            << maxOverlap << " characters to generate " << merged << std::endl;
        fsCurr[maxOverlapIndex] = merged;
      }
      else
      {
        fsCurr.push_back(f);
      }
    }
    if (fitSetLenSum > len)
    {
      Trace("str-anon-graph")
          << "**** could not merge " << fsCurr << " to " << len << std::endl;
    }
  }
  // now, add if
  if (fitSetLenSum <= len)
  {
    // simple case, add slack and randomly arrange
    for (unsigned i = 0; i < (len - fitSetLenSum); i++)
    {
      Node randChar = randomLiteral(base, 1);
      fsCurr.push_back(randChar);
    }
    std::shuffle(fsCurr.begin(), fsCurr.end(), Random::getRandom());
  }
  std::vector<unsigned> vec;
  for (const Node& f : fsCurr)
  {
    const std::vector<unsigned>& fvec = f.getConst<String>().getVec();
    vec.insert(vec.end(), fvec.begin(), fvec.end());
  }
  // remove a suffix if we failed to shrink
  if (vec.size() > len && options::anonymizeStringsPreserveLengths())
  {
    vec.erase(vec.begin() + len, vec.end());
  }
  return nm->mkConst(String(vec));
}

unsigned analyzeSolutionNode(Node l,
                             CtnNode& cl,
                             Node lSol,
                             const Graph& graphCheck,
                             const std::map<Node, Node>& sol)
{
  unsigned falseCtn[2] = {0, 0};
  unsigned trueCtn[2] = {0, 0};
  String ls = l.getConst<String>();
  String sls = lSol.getConst<String>();
  for( unsigned r=0; r<2; r++ )
  {
    // check the base nodes of the graph check
    for( const Node& lc : graphCheck.d_baseNodes[r] )
    {
      String lcs = lc.getConst<String>();
      std::map< Node, Node >::const_iterator its = sol.find(lc);
      Assert( its!=sol.end() );
      String slcs = its->second.getConst<String>();
      bool origRel = false;
      bool solRel = false;
      if( r==0 )
      {
        origRel = ls.find(lcs)!=std::string::npos; 
        solRel = sls.find(slcs)!=std::string::npos; 
      }
      else
      {
        origRel = lcs.find(ls)!=std::string::npos; 
        solRel = slcs.find(sls)!=std::string::npos; 
      }
      if( origRel!=solRel )
      {
        falseCtn[r]++;
      }
      else
      {
        trueCtn[r]++;
      }
    }
  }
  
  return falseCtn[0] + falseCtn[1];
}

unsigned analyzeSolution(const std::vector<Node>& litSet,
                         const std::map<Node, Node>& sol,
                         const Graph& graph,
                         const Graph& graphCheck
                        )
{
  unsigned falseCtn[2] = {0, 0};
  unsigned trueCtn[2] = {0, 0};

  // check graph vs graphCheck
  for (const Node& l : litSet)
  {
    std::map<Node, CtnNode>::const_iterator itl = graph.d_graph.find(l);
    Assert(itl != graph.d_graph.end());
    std::map<Node, CtnNode>::const_iterator itlc = graphCheck.d_graph.find(l);
    Assert(itlc != graphCheck.d_graph.end());
    const std::unordered_set<Node, NodeHashFunction>& c =
        itl->second.d_edges[0];
    const std::unordered_set<Node, NodeHashFunction>& cc =
        itlc->second.d_edges[0];
    for (unsigned e = 0; e < 2; e++)
    {
      const std::unordered_set<Node, NodeHashFunction>& chc = e == 0 ? c : cc;
      const std::unordered_set<Node, NodeHashFunction>& chco = e == 0 ? cc : c;
      bool hasError = false;
      for (const Node& lc : chc)
      {
        if (std::find(chco.begin(), chco.end(), lc) == chco.end())
        {
          hasError = true;
          falseCtn[e]++;
          if (Trace.isOn("str-anon-solve-debug"))
          {
            Trace("str-anon-solve-debug")
                << "  * Warn: " << l << (e == 0 ? " >> " : " << ") << lc
                << " but values do not respect this relationship:" << std::endl;
            std::map<Node, Node>::const_iterator itsl = sol.find(l);
            Assert(itsl != sol.end());
            std::map<Node, Node>::const_iterator itslc = sol.find(lc);
            Assert(itslc != sol.end());
            Trace("str-anon-solve-debug") << "    " << itsl->second << " <> "
                                          << itslc->second << std::endl;
          }
        }
        else
        {
          trueCtn[e]++;
        }
      }
      // no need to check opposite if they are the same size and first is subset
      if (e == 0 && !hasError && c.size() == cc.size())
      {
        trueCtn[1] += c.size();
        break;
      }
    }
  }
  Trace("str-anon-solve") << "Solve:  Analyze false ctn: " << falseCtn[0]
                          << " / " << (trueCtn[0]+falseCtn[0]) << std::endl;
  Trace("str-anon-solve") << "Solve:  Analyze false non-ctn: " << falseCtn[1]
                          << " / " << (trueCtn[1]+falseCtn[1]) << std::endl;
  
  return falseCtn[0] + falseCtn[1];
}

void approxSolveGraph(Graph& graph, Graph& graphCheck,std::map<Node, Node>& sol)
{
  unsigned areps = options::anonymizeStringsEffortLocal();
  Trace("str-anon-graph") << "Approximately solve graph..." << std::endl;
  // get the unprocessed nodes
  std::unordered_set<Node, NodeHashFunction> nextToProcess;
  std::unordered_set<Node, NodeHashFunction> toProcess = graph.d_baseNodes[0];
  do
  {
    for (const Node& l : toProcess)
    {
      if (sol.find(l) != sol.end())
      {
        // already processed
        continue;
      }
      Assert(graph.d_graph.find(l) != graph.d_graph.end());
      CtnNode& cl = graph.d_graph[l];
      // Are we ready to process this? Must be that all children are processed.
      bool ready = true;
      std::vector<Node> fitSet;
      unsigned fitSetLenSum = 0;
      std::map<Node, Node>::iterator itf;
      for (const Node& cp : cl.d_edges[0])
      {
        itf = sol.find(cp);
        if (itf == sol.end())
        {
          ready = false;
          break;
        }
        if (!options::anonymizeStringsPreserveCtn())
        {
          // do not fit anything if we aren't preserving containment
          continue;
        }
        Node cps = itf->second;
        // add if not duplicate
        if (std::find(fitSet.begin(), fitSet.end(), cps) == fitSet.end())
        {
          fitSet.push_back(cps);
          fitSetLenSum += cps.getConst<String>().size();
        }
      }
      if (!ready)
      {
        // not ready to process, we wait.
        nextToProcess.insert(l);
        continue;
      }
      // otherwise, the parents of this may be next to process
      std::unordered_set<Node, NodeHashFunction>& clp = cl.d_edges[1];
      nextToProcess.insert(clp.begin(), clp.end());

      // construct the solution for the current string
      Node lSol;
      unsigned bestScore = 0;
      std::unordered_set< Node, NodeHashFunction > lscProc;
      Trace("str-anon-solve-local") << "Try assign " << l << std::endl;
      for (unsigned r = 0; r < areps; r++)
      {
        Node lsc = approxSolveNode(l, cl, fitSet, fitSetLenSum);
        if( lscProc.find(lsc)!=lscProc.end() )
        {
          // already tried
          continue;
        }
        lscProc.insert(lsc);
        unsigned score = areps==1 ? 0 : analyzeSolutionNode(l, cl, lsc, graphCheck, sol);
        Trace("str-anon-solve-local") << "  Score " << lsc << " is " << score << std::endl;
        if (r == 0 || score < bestScore)
        {
          bestScore = score;
          lSol = lsc;
          if( score==0 )
          {
            // cannot improve
            break;
          }
        }
      }
      sol[l] = lSol;
      graphCheck.add(l,sol);
      Trace("str-anon-graph")
          << "  Assign: " << l << " -> " << lSol << std::endl;
    }
    toProcess.clear();
    toProcess.insert(nextToProcess.begin(), nextToProcess.end());
    nextToProcess.clear();
  } while (!toProcess.empty());
}

bool solveAnonStrGraph(
    const std::unordered_map<Node, Node, NodeHashFunction>& lits,
    std::unordered_map<Node, Node, NodeHashFunction>& substs)
{
  std::vector<Node> litSet;
  for (const std::pair<const Node, Node>& ls : lits)
  {
    litSet.push_back(ls.first);
  }

  Trace("str-anon-graph") << "String literals: " << lits << std::endl;

  // ------------ construct the graph

  // maximal children, parents
  Graph graph;
  graph.build(litSet);

  // ------------ solve for the graph
  unsigned nreps = options::anonymizeStringsEffort();
  std::map<Node, Node> bestSol;
  unsigned bestScore = 0;
  for (unsigned r = 0; r < nreps; r++)
  {
    Trace("str-anon-solve") << "Solve: Solve #" << r << "..." << std::endl;
    Graph graphCheck;
    std::map<Node, Node> sol;
    approxSolveGraph(graph, graphCheck, sol);

    Trace("str-anon-solve") << "Solve: Analyze #" << r << "..." << std::endl;
    unsigned score = analyzeSolution(litSet, sol, graph, graphCheck);
    Trace("str-anon-solve") << "Solve: ...score=" << score << std::endl;
    if (r == 0 || score < bestScore)
    {
      Trace("str-anon-solve") << "Solve: new best!" << std::endl;
      bestScore = score;
      bestSol = sol;
      if( score==0 )
      {
        // cannot improve
        break;
      }
    }
  }

  // copy to substitution
  for (const std::pair<const Node, Node>& bs : bestSol)
  {
    substs[bs.first] = bs.second;
  }

  return true;
}

/// ---------------------------------------------------------------

Node collectLits( Node n,
                 std::unordered_map<Node, Node, NodeHashFunction>* lits,
                 std::unordered_set<Node, NodeHashFunction>* reranges ){
  NodeManager * nm = NodeManager::currentNM();
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
      for (const Node& cn : cur )
      {
        visit.push_back(cn);
      }
    } 
    else if (it->second.isNull()) 
    {
      Node ret = cur;
      if (cur.getKind() == kind::CONST_STRING)
      {
        if (cur.getConst<String>().size() > 0)
        {
          if (lits->find(cur) == lits->end())
          {
            (*lits)[cur] = nm->mkSkolem("s", nm->stringType());
          }
        }
      }
      else if (cur.getKind() == kind::REGEXP_RANGE)
      {
        reranges->insert(cur);
      }
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur )
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
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}


std::unordered_map<Node, std::vector<Node>, NodeHashFunction>
computeContainsRels(
    const std::unordered_map<Node, Node, NodeHashFunction>& lits)
{
  std::unordered_map<Node, std::vector<Node>, NodeHashFunction> containsRels;
  for (const auto& kv : lits)
  {
    // Make sure that each literal is a key
    containsRels[kv.second];
  }

  for (const auto& kv1 : lits)
  {
    for (const auto& kv2 : lits)
    {
      Node s1 = kv1.first;
      Node s2 = kv2.first;
      if (kv1.first != kv2.first)
      {
        if (s1.getConst<String>().find(s2.getConst<String>())
            != std::string::npos)
        {
          containsRels[kv1.second].push_back(kv2.second);
        }
      }
    }
  }
  return containsRels;
}

bool isNotCtn(
    Node t,
    Node s,
    const std::unordered_map<Node, std::vector<Node>, NodeHashFunction>&
        containsRels)
{
  std::vector<Node> toVisit = containsRels.at(t);
  while (!toVisit.empty())
  {
    Node curr = toVisit.back();
    toVisit.pop_back();

    Assert(curr != t);
    if (curr == s)
    {
      return false;
    }
    else
    {
      toVisit.insert(toVisit.end(),
                     containsRels.at(curr).begin(),
                     containsRels.at(curr).end());
    }
  }

  return true;
}

void indirectContains(
    const std::unordered_map<Node, std::vector<Node>, NodeHashFunction>&
        containsRels,
    Node t,
    std::unordered_set<Node, NodeHashFunction>& res)
{
  res.insert(t);
  for (const Node& n : containsRels.at(t))
  {
    indirectContains(containsRels, n, res);
  }
}

bool needNegCtn(
    Node t,
    Node s,
    const std::unordered_map<Node, std::vector<Node>, NodeHashFunction>&
        containsRels)
{
  /*return true;
  if (!containsRels.at(s).empty()) {
    std::cout << "Unnecessary neg ctn: " << s << " " << t << std::endl;
  }*/

  std::unordered_set<Node, NodeHashFunction> ic;
  indirectContains(containsRels, t, ic);

  for (const Node& n : containsRels.at(s))
  {
    if (ic.find(n) != ic.end())
    {
      return true;
    }
  }

  return containsRels.at(s).empty();
}

std::vector<Node> mkQueries(
    const std::unordered_map<Node, Node, NodeHashFunction>& lits,
    const std::unordered_map<Node, std::vector<Node>, NodeHashFunction>&
        containsRels)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> queries;

  std::unordered_map<Node, size_t, NodeHashFunction> lengths;
  unsigned i = 0;
  if (options::anonymizeStringsPreserveLengths())
  {
    for (const auto& kv : lits)
    {
      size_t length = kv.first.getConst<String>().size();
      lengths[kv.second] = length;
      queries.push_back(nm->mkNode(kind::EQUAL,
                                   nm->mkNode(kind::STRING_LENGTH, kv.second),
                                   nm->mkConst(Rational(length))));

      if (length == 1)
      {
        queries.push_back(
            nm->mkNode(kind::EQUAL,
                       kv.second,
                       nm->mkConst(String(std::vector<unsigned>{i}))));
        i++;
      }
    }
  }

  for (const auto& kv : containsRels)
  {
    for (const Node& containee : kv.second)
    {
      queries.push_back(nm->mkNode(kind::STRING_STRCTN, kv.first, containee));
    }
  }

  if (containsRels.size() > 1)
  {
    if (options::anonymizeStringsUseDistinct())
    {
      // Distinct strings constraints
      std::vector<Node> vars;
      for (const auto& kv : containsRels)
      {
        vars.push_back(kv.first);
      }
      queries.push_back(nm->mkNode(kind::DISTINCT, vars));
    }
    else
    {
      // Negative contains constraints
      for (const auto& kv1 : containsRels)
      {
        for (const auto& kv2 : containsRels)
        {
          if (kv1.first != kv2.first
              && isNotCtn(kv1.first, kv2.first, containsRels))
          {
            if (needNegCtn(kv1.first, kv2.first, containsRels))
            {
              if (!options::anonymizeStringsPreserveLengths()
                  || lengths[kv1.first] > lengths[kv2.first])
              {
                queries.push_back(nm->mkNode(
                    kind::NOT,
                    nm->mkNode(kind::STRING_STRCTN, kv1.first, kv2.first)));
              }
              else if (lengths[kv1.first] == lengths[kv2.first])
              {
                queries.push_back(nm->mkNode(
                    kind::NOT, nm->mkNode(kind::EQUAL, kv1.first, kv2.first)));
              }
            }
          }
        }
      }
    }
  }
  return queries;
}

bool solveAnonStrQuery(
    const std::unordered_map<Node, Node, NodeHashFunction>& lits,
    std::unordered_map<Node, Node, NodeHashFunction>& substs)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, std::vector<Node>, NodeHashFunction> containsRels =
      computeContainsRels(lits);

  Trace("anonymize-strings")
      << "Contains relationships: " << containsRels << std::endl;

  std::vector<Node> queries = mkQueries(lits, containsRels);

  Trace("anonymize-strings") << "Queries: " << queries << std::endl;

  bool dumpBenchmark = Dump.isOn("anonymization-benchmark");

  SmtEngine checker(nm->toExprManager());
  checker.setIsInternalSubsolver();
  {
    smt::SmtScope smts(&checker);

    if (Dump.isOn("anonymization-benchmark"))
    {
      Dump.on("raw-benchmark");
    }
    else
    {
      Dump.off();
    }
  }

  // checker.setOption("anonymize-strings", false);
  // checker.setOption("preprocess-only", false);
  // checker.setOption("produce-models", true);

  ExprManagerMapCollection varMap;
  for (const Node& query : queries)
  {
    Expr equery = query.toExpr();
    checker.assertFormula(equery);
  }

  if (dumpBenchmark)
  {
    // HACK
    std::cout << "(check-sat)" << std::endl;
    Dump.off();
    return false;
  }
  else
  {
    checker.checkSat();
  }

  Trace("anonymize-strings") << "Values:" << std::endl;
  for (const auto& kv : lits)
  {
    Expr esk = kv.second.toExpr();
    substs[kv.first] = Node::fromExpr(checker.getValue(esk));
    Trace("anonymize-strings") << "..." << kv.second << " = " << kv.first
                               << " -> " << checker.getValue(esk) << std::endl;
  }
  return true;
}

}  // namespace

AnonymizeStrings::AnonymizeStrings(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "anonymize-strings"){};

PreprocessingPassResult AnonymizeStrings::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::unordered_map<Node, Node, NodeHashFunction> lits;
  std::unordered_set<Node, NodeHashFunction> reranges;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    collectLits((*assertionsToPreprocess)[i], &lits, &reranges);
  }

  Trace("anonymize-strings")
      << "String literal skolem map: " << lits << std::endl;

  std::unordered_map<Node, Node, NodeHashFunction> substs;
  bool madeSol = false;
  if (options::anonymizeStringsQuery())
  {
    madeSol = solveAnonStrQuery(lits, substs);
  }
  else
  {
    madeSol = solveAnonStrGraph(lits, substs);
  }
  if (!madeSol)
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }

  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, TNode, TNodeHashFunction> cache;
  std::unordered_map<TNode, TNode, TNodeHashFunction> rcache;
  // fix the re ranges as a second substitution
  std::unordered_map<Node, Node, NodeHashFunction> rerangeSubsts;
  for (const Node& rr : reranges)
  {
    Node nrr = rr.substitute(substs.begin(), substs.end(), cache);
    String rr0s = rr[0].getConst<String>();
    String rr1s = rr[1].getConst<String>();
    Assert(rr1s.getVec()[0] > rr0s.getVec()[0]);
    unsigned rdiff = rr1s.getVec()[0] - rr0s.getVec()[0];
    // try to go the direction that doesn't cause out of bounds
    Node nrr0 = nrr[0];
    Node nrr1 = nrr[1];
    String nrr0s = nrr0.getConst<String>();
    String nrr1s = nrr1.getConst<String>();
    if (nrr0s.getVec()[0] + rdiff < String::num_codes())
    {
      std::vector<unsigned> vec;
      vec.push_back(nrr0s.getVec()[0] + rdiff);
      nrr1 = nm->mkConst(String(vec));
    }
    else if (nrr1s.getVec()[0] > rdiff)
    {
      std::vector<unsigned> vec;
      vec.push_back(nrr1s.getVec()[0] - rdiff);
      nrr0 = nm->mkConst(String(vec));
    }
    // otherwise don't bother fixing
    Node nrrf = nm->mkNode(kind::REGEXP_RANGE, nrr0, nrr1);
    Trace("anon-str") << "*** Fix RE range: " << nrr << " -> " << nrrf
                      << ", from " << rr << std::endl;
    rerangeSubsts[nrr] = nrrf;
  }

  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node currA = (*assertionsToPreprocess)[i];
    Node newA = currA.substitute(substs.begin(), substs.end(), cache);
    if (!rerangeSubsts.empty())
    {
      newA =
          newA.substitute(rerangeSubsts.begin(), rerangeSubsts.end(), rcache);
    }
    assertionsToPreprocess->replace(i, newA);

    // HACK!!!!
    std::cout << "(assert " << (*assertionsToPreprocess)[i] << ")" << std::endl;
  }

  // HACK!!!!
  // std::cout << "(check-sat)" << std::endl;

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
