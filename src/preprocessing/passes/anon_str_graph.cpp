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

#include "preprocessing/passes/anon_str_graph.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

void CtnNode::getTransitiveClosure(
    Graph& graph, std::unordered_set<Node, NodeHashFunction>& t, unsigned dir)
{
  if (t.find(d_this) != t.end())
  {
    // already processed
    return;
  }
  t.insert(d_this);
  for (const Node& c : d_edges[dir])
  {
    Assert(graph.d_graph.find(c) != graph.d_graph.end());
    graph.d_graph[c].getTransitiveClosure(graph, t, dir);
  }
}
void CtnNode::debugPrint(const char* c) const
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

void CtnNode::removeEdge(Graph& graph, Node c, unsigned dir)
{
  Assert(d_edges[dir].find(c) != d_edges[dir].end());
  d_edges[dir].erase(c);
  Assert(graph.d_graph.find(c) != graph.d_graph.end());
  CtnNode& cc = graph.d_graph[c];
  Assert(cc.d_edges[1 - dir].find(d_this) != cc.d_edges[1 - dir].end());
  cc.d_edges[1 - dir].erase(d_this);
}

std::map<Node, Node> Graph::d_emptyMap;

void Graph::build(const std::vector<Node>& litSet)
{
  build(litSet, d_emptyMap);
}
void Graph::build(const std::vector<Node>& litSet,
                  const std::map<Node, Node>& valMap)
{
  for (const Node& l : litSet)
  {
    add(l, valMap);
  }
  // print
  if (Trace.isOn("str-anon-graph"))
  {
    for (const std::pair<const Node, CtnNode>& c : d_graph)
    {
      c.second.debugPrint("str-anon-graph");
    }
  }
}
void Graph::add(Node l) { add(l, d_emptyMap); }
void Graph::add(Node l, const std::map<Node, Node>& valMap)
{
  Trace("str-anon-graph") << "Add literal " << l << std::endl;
  CtnNode& cl = d_graph[l];
  cl.d_this = l;
  std::unordered_set<Node, NodeHashFunction> transCtn;
  // process downward, upward
  for (unsigned dir = 0; dir <= 1; dir++)
  {
    std::unordered_set<Node, NodeHashFunction> processed;
    // add to graph
    std::unordered_set<Node, NodeHashFunction> toProcess = d_baseNodes[1 - dir];
    addInternal(l, cl, toProcess, dir, processed, transCtn, valMap);
  }
  Trace("str-anon-graph-debug") << std::endl;
}

void Graph::addInternal(Node l,
                        CtnNode& cl,
                        std::unordered_set<Node, NodeHashFunction>& toProcess,
                        unsigned dir,
                        std::unordered_set<Node, NodeHashFunction>& processed,
                        std::unordered_set<Node, NodeHashFunction>& transCtn,
                        const std::map<Node, Node>& valMap)
{
  Node lv = l;
  std::map<Node, Node>::const_iterator itv = valMap.find(l);
  if (itv != valMap.end())
  {
    lv = itv->second;
  }
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
      Assert(d_graph.find(lp) != d_graph.end());
      CtnNode& clp = d_graph[lp];
      bool ready = true;
      for (const Node& cp : clp.d_edges[1 - dir])
      {
        if (processed.find(cp) == processed.end())
        {
          ready = false;
          break;
        }
      }
      if (!ready)
      {
        // not ready to process, we wait.
        nextToProcess.insert(lp);
        continue;
      }
      processed.insert(lp);
      Trace("str-anon-graph-debug")
          << "- check " << l << (dir == 0 ? " << " : " >> ") << lp << std::endl;
      bool isEdge = false;
      // get the value for lp
      Node lpv = lp;
      itv = valMap.find(lp);
      if (itv != valMap.end())
      {
        lpv = itv->second;
      }
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
          isEdge = (lpv.getConst<String>().find(lv.getConst<String>())
                    != std::string::npos);
        }
      }
      else
      {
        isEdge = (lv.getConst<String>().find(lpv.getConst<String>())
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
        clp.getTransitiveClosure(*this, tc, dir);
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
                Assert(d_graph.find(lc) != d_graph.end());
                CtnNode& clc = d_graph[lc];
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

  // if dir=0, if it has no children, it is a maximal child
  // if dir=1, if it has no parents, it is a maximal parent
  std::unordered_set<Node, NodeHashFunction>& edges = cl.d_edges[dir];
  if (edges.empty())
  {
    d_baseNodes[dir].insert(l);
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
      if (d_baseNodes[1 - dir].find(e) != d_baseNodes[1 - dir].end())
      {
        Trace("str-anon-graph-debug")
            << "--- " << e << " is no long base node dir=" << (1 - dir)
            << std::endl;
        d_baseNodes[1 - dir].erase(e);
      }
    }
  }
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
