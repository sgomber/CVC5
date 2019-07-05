/*********************                                                        */
/*! \file anonymize_strings.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Caleb Donovick
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

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

namespace {

class CtnNode
{
 public:
  Node d_this;
  /** 0:children, 1:parents */
  std::unordered_set<Node, NodeHashFunction> d_edges[2];

  void getTransitiveClosure(std::map<Node, CtnNode>& graph,
                            std::unordered_set<Node, NodeHashFunction>& t,
                            unsigned dir)
  {
    if (t.find(d_this) != t.end())
    {
      // already processed
      return;
    }
    t.insert(d_this);
    for (const Node& c : d_edges[dir])
    {
      Assert(graph.find(c) != graph.end());
      graph[c].getTransitiveClosure(graph, t, dir);
    }
  }
  void debugPrint(const char* c) const
  {
    Trace(c) << "Node(" << d_this << "):" << std::endl;
    for (unsigned dir = 0; dir <= 1; dir++)
    {
      Trace(c) << "  " << (dir == 0 ? "children:" : "parent:") << " ";
      for (const Node& e : d_edges[dir])
      {
        Trace(c) << e << " ";
      }
      Trace(c) << std::endl;
    }
  }

  void removeEdge(std::map<Node, CtnNode>& graph, Node c, unsigned dir)
  {
    Assert(d_edges[dir].find(c) != d_edges[dir].end());
    d_edges[dir].erase(c);
    Assert(graph.find(c) != graph.end());
    CtnNode& cc = graph[c];
    Assert(cc.d_edges[1 - dir].find(d_this) != cc.d_edges[1 - dir].end());
    cc.d_edges[1 - dir].erase(d_this);
  }
};

void addToGraph(Node l,
                CtnNode& cl,
                std::map<Node, CtnNode>& graph,
                std::unordered_set<Node, NodeHashFunction>& toProcess,
                unsigned dir,
                std::unordered_set<Node, NodeHashFunction>& processed,
                std::unordered_set<Node, NodeHashFunction>& transCtn)
{
  std::unordered_set<Node, NodeHashFunction> nextToProcess;
  do
  {
    for (const Node& lp : toProcess)
    {
      if (l == lp)
      {
        // ignore self
        continue;
      }
      if (processed.find(lp) != processed.end())
      {
        // already processed
        continue;
      }
      // Now, check if we are ready to process this.
      // To be ready, we need for each of its parents/children to have been
      // processed. This ensures we process only "maximal" nodes with respect
      // to the set of nodes that are unprocessed, which in turn means we don't
      // add edges to nodes that we later could find to be implied by 
      // transitivity.
      Assert(graph.find(lp) != graph.end());
      CtnNode& clp = graph[lp];
      bool ready = true;
      for( const Node& cp : clp.d_edges[1-dir] )
      {
        if( processed.find( cp )==processed.end() )
        {
          ready = false;
          break;
        }
      }
      if( !ready )
      {
        // not ready to process, we wait.
        nextToProcess.insert(lp);
        continue;
      }
      processed.insert(lp);
      Trace("str-anon-graph-debug")
          << "- check " << l << (dir == 0 ? " << " : " >> ") << lp << std::endl;
      bool isEdge = false;
      if (dir == 1)
      {
        if (transCtn.find(lp) != transCtn.end())
        {
          Trace("str-anon-graph-debug")
              << "...already descendant!" << std::endl;
        }
        else
        {
          // only check if we don't contain it, since contains is antisymmetric
          isEdge = (lp.getConst<String>().find(l.getConst<String>())
                    != std::string::npos);
        }
      }
      else
      {
        isEdge = (l.getConst<String>().find(lp.getConst<String>())
                  != std::string::npos);
      }
      if (isEdge)
      {
        Trace("str-anon-graph-debug") << "...edge!" << std::endl;
        // add edge to graph
        cl.d_edges[dir].insert(lp);
        clp.d_edges[1 - dir].insert(l);
        // compute transitive closure
        std::unordered_set<Node, NodeHashFunction> tc;
        clp.getTransitiveClosure(graph, tc, dir);
        // add transitive closure to processed
        processed.insert(tc.begin(), tc.end());
        if (dir == 0)
        {
          // remember it here
          transCtn.insert(tc.begin(), tc.end());
        }
        else
        {
          // if they have common children/parent, we de-transify it
          for (unsigned dirl = 0; dirl <= 1; dirl++)
          {
            std::unordered_set<Node, NodeHashFunction>& lpc = clp.d_edges[dirl];
            std::vector<Node> toErase;
            for (const Node& lc : cl.d_edges[dirl])
            {
              if (lpc.find(lc) != lpc.end())
              {
                Trace("str-anon-graph-debug")
                    << "--- Detransify " << l << ", " << lp
                    << (dirl == 0 ? " << " : " >> ") << lc << std::endl;
                // they have a common child/parent, remove transitive edge
                Assert(graph.find(lc) != graph.end());
                CtnNode& clc = graph[lc];
                if (dirl == 0)
                {
                  lpc.erase(lc);
                  Assert(clc.d_edges[1 - dirl].find(lp)
                         != clc.d_edges[1 - dirl].end());
                  clc.d_edges[1 - dirl].erase(lp);
                }
                else
                {
                  toErase.push_back(lc);
                  Assert(clc.d_edges[1 - dirl].find(l)
                         != clc.d_edges[1 - dirl].end());
                  clc.d_edges[1 - dirl].erase(l);
                }
              }
            }
            // now out of the loop, erase
            for (const Node& lc : toErase)
            {
              cl.d_edges[dirl].erase(lc);
            }
          }
        }
      }
      else
      {
        // add next to processed
        std::unordered_set<Node, NodeHashFunction>& lpp = clp.d_edges[dir];
        Trace("str-anon-graph-debug") << "...not edge!" << std::endl;
        nextToProcess.insert(lpp.begin(), lpp.end());
      }
    }
    toProcess.clear();
    toProcess.insert(nextToProcess.begin(), nextToProcess.end());
    nextToProcess.clear();
  } while (!toProcess.empty());
}

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

void approxSolveGraph(std::map<Node, CtnNode>& graph,
                      const std::unordered_set<Node, NodeHashFunction>& baseChild,
                      std::map<Node, Node>& sol)
{
  Trace("str-anon-graph") << "Approximately solve graph..." << std::endl;
  unsigned base = 26;
  NodeManager * nm = NodeManager::currentNM();
  // get the unprocessed nodes
  std::unordered_set<Node, NodeHashFunction> nextToProcess;
  std::unordered_set<Node, NodeHashFunction> toProcess = baseChild;
  do
  {
    for( const Node& l : toProcess )
    {
      if( sol.find(l)!=sol.end() )
      {
        // already processed
        continue;
      }
      Assert(graph.find(l) != graph.end());
      CtnNode& cl = graph[l];      
      // Are we ready to process this? Must be that all children are processed.
      bool ready = true;
      std::vector< Node > fitSet;
      unsigned fitSetLenSum = 0;
      std::map< Node, Node >::iterator itf;
      for( const Node& cp : cl.d_edges[0] )
      {
        itf = sol.find( cp );
        if( itf==sol.end() )
        {
          ready = false;
          break;
        }
        Node cps = itf->second;
        // add if not duplicate
        if( std::find( fitSet.begin(), fitSet.end(), cps )==fitSet.end() )
        {
          fitSet.push_back(cps);
          fitSetLenSum += cps.getConst<String>().size();
        }
      }
      if( !ready )
      {
        // not ready to process, we wait.
        nextToProcess.insert(l);
        continue;
      }
      // otherwise, the parents of this may be next to process
      std::unordered_set<Node, NodeHashFunction>& clp = cl.d_edges[1];
      nextToProcess.insert(clp.begin(),clp.end());
      
      // construct the solution for the current string
      Node lSol;
      Assert( l.isConst() );
      unsigned len = l.getConst<String>().size();
      // try to pack the fit set into the string's length
      if( fitSet.empty() )
      {
        // base case, it is a random value
        lSol = randomLiteral(base, len);
      }
      else
      {
        if( fitSetLenSum<=len )
        {
          // simple case, add slack and randomly arrange
          for( unsigned i=0; i<(len-fitSetLenSum); i++ )
          {
            Node randChar = randomLiteral(base,1);
            fitSet.push_back(randChar);
          }
          std::shuffle(fitSet.begin(), fitSet.end(), Random::getRandom());
        }
        else
        {
          // try to fit based on overlaps TODO
          Trace("str-anon-graph") << "********* Need fit for " << l << std::endl;
          // first, randomize
          std::shuffle(fitSet.begin(), fitSet.end(), Random::getRandom());
          // now, compute overlaps
          
        }
        std::vector< unsigned > vec;
        for( const Node& f : fitSet )
        {
          const std::vector< unsigned >& fvec = f.getConst<String>().getVec();
          vec.insert(vec.end(),fvec.begin(),fvec.end());
        }
        // TODO: remove
        if( vec.size()>len )
        {
          vec.erase( vec.begin()+len, vec.end());
        }
        lSol = nm->mkConst(String(vec));
      }
      sol[l] = lSol;
      Trace("str-anon-graph") << "  Assign: " << l << " -> " << lSol << std::endl;
    }
    toProcess.clear();
    toProcess.insert(nextToProcess.begin(),nextToProcess.end());
    nextToProcess.clear();
  }while( !toProcess.empty() );
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
  std::unordered_set<Node, NodeHashFunction> baseNodes[2];
  std::map<Node, CtnNode> graph;

  for (const Node& l : litSet)
  {
    Trace("str-anon-graph") << "Process literal " << l << std::endl;
    CtnNode& cl = graph[l];
    cl.d_this = l;
    std::unordered_set<Node, NodeHashFunction> transCtn;
    // process downward, upward
    for (unsigned dir = 0; dir <= 1; dir++)
    {
      std::unordered_set<Node, NodeHashFunction> processed;
      // add to graph
      std::unordered_set<Node, NodeHashFunction> toProcess = baseNodes[1 - dir];
      addToGraph(l, cl, graph, toProcess, dir, processed, transCtn);
      // if dir=0, if it has no children, it is a maximal child
      // if dir=1, if it has no parents, it is a maximal parent
      std::unordered_set<Node, NodeHashFunction>& edges = cl.d_edges[dir];
      if (edges.empty())
      {
        baseNodes[dir].insert(l);
        Trace("str-anon-graph-debug")
            << "*** it is a base node, dir=" << dir << std::endl;
      }
      else
      {
        Trace("str-anon-graph-debug") << "*** it has " << edges.size()
                                      << " edges with dir=" << dir << std::endl;
        // update base nodes
        for (const Node& e : edges)
        {
          if (baseNodes[1 - dir].find(e) != baseNodes[1 - dir].end())
          {
            Trace("str-anon-graph-debug")
                << "--- " << e << " is no long base node dir=" << (1 - dir)
                << std::endl;
            baseNodes[1 - dir].erase(e);
          }
        }
      }
    }
    Trace("str-anon-graph-debug") << std::endl;
  }
  // print
  if (Trace.isOn("str-anon-graph"))
  {
    for (const std::pair<const Node, CtnNode>& c : graph)
    {
      c.second.debugPrint("str-anon-graph");
    }
  }

  // ------------ solve for the graph
  unsigned nreps = 1;
  std::map<Node, Node> bestSol;
  for (unsigned r = 0; r < nreps; r++)
  {
    std::map<Node, Node> sol;
    approxSolveGraph(graph, baseNodes[0], sol);
    // TODO
    bool isBest = true;
    
    if( isBest )
    {
      bestSol = sol;
    }
  }
  
  // copy to substitution
  for( const std::pair< const Node, Node >& bs : bestSol )
  {
    substs[bs.first] = bs.second;
  }
  

  return true;
}

/// ---------------------------------------------------------------

void collectLits(Node n, std::unordered_map<Node, Node, NodeHashFunction>* lits)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::unordered_map<TNode, bool, TNodeHashFunction>::iterator it;
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
      visited[cur] = false;

      visit.push_back(cur);
      for (unsigned i = 0; i < cur.getNumChildren(); i++)
      {
        visit.push_back(cur[i]);
      }
    }
    else if (!it->second)
    {
      if (cur.getKind() == kind::CONST_STRING
          && cur.getConst<String>().size() > 0)
      {
        if (lits->find(cur) == lits->end())
        {
          (*lits)[cur] = nm->mkSkolem("s", nm->stringType());
        }
      }
      visited[cur] = true;
    }
  } while (!visit.empty());
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
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    collectLits((*assertionsToPreprocess)[i], &lits);
  }

  Trace("anonymize-strings")
      << "String literal skolem map: " << lits << std::endl;

  std::unordered_map<Node, Node, NodeHashFunction> substs;
  if (!solveAnonStrGraph(lits, substs))
  {
    return PreprocessingPassResult::NO_CONFLICT;
  }

  std::unordered_map<TNode, TNode, TNodeHashFunction> cache;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(i,
                                    (*assertionsToPreprocess)[i].substitute(
                                        substs.begin(), substs.end(), cache));

    // HACK!!!!
    std::cout << "(assert " << (*assertionsToPreprocess)[i] << ")" << std::endl;
  }

  // HACK!!!!
  std::cout << "(check-sat)" << std::endl;

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
