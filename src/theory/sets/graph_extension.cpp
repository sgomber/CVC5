/*********************                                                        */
/*! \file graph_extension.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of an extension of the sets theory that specializes in
 ** finite graphs.
 **/

#include "theory/sets/graph_extension.h"

#include "expr/datatype.h"
#include "theory/sets/normal_form.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

GraphExtension::GraphExtension(SolverState& s,
                               InferenceManager& im,
                               eq::EqualityEngine& e,
                               context::Context* c,
                               context::UserContext* u)
    : d_state(s), d_im(im), d_ee(e)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

GraphExtension::~GraphExtension() {}

void GraphExtension::preRegisterTerm(TNode node)
{
  Trace("graph") << "GraphExtension::preRegisterTerm: " << node << std::endl;
  Kind k = node.getKind();
  if (k == MEMBER)
  {
    // ensure correct form
    checkEdge(node[0]);
    TNode g = node[1];
    if (g.getKind() == TCLOSURE)
    {
      g = g[0];
    }
    checkGraphVariable(g);
  }
  else if (k == SUBSET)
  {
    checkGraphVariable(node[0]);
    collectElements(node[1], node[0]);
  }
  else if (k == EQUAL)
  {
    // equalities between sets are not handled
    if (node[0].getType().isSet())
    {
      std::stringstream ss;
      ss << "GraphExtension: Cannot handle equality between sets " << node;
      throw LogicException(ss.str());
    }
  }
}

void GraphExtension::assertFact(TNode fact, TNode exp)
{
  if (Trace.isOn("graph"))
  {
    Trace("graph") << "GraphExtension::assertNode: " << fact << std::endl;
    if (fact != exp)
    {
      Trace("graph") << "  with explanation " << exp << std::endl;
    }
  }
}

void GraphExtension::check(Theory::Effort level)
{
  Trace("graph") << "GraphExtension::check: " << level << std::endl;
}

void GraphExtension::collectElements(TNode val, TNode g)
{
  GraphInfo& gi = d_ginfo[g];
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(val);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.getKind() == UNION)
      {
        for (TNode cn : cur)
        {
          visit.push_back(cn);
        }
      }
      else if (cur.getKind() == SINGLETON)
      {
        // cur[0] should be a constant tuple (c1, c2).
        checkEdge(cur[0]);
        gi.addEdge(cur[0][0], cur[0][1]);
        Trace("graph-info") << "Edge: (" << cur[0][0] << ", " << cur[0][1]
                            << ") ?in " << g << std::endl;
      }
      else
      {
        std::stringstream ss;
        ss << "GraphExtension: Cannot handle non-constant in subset "
              "restriction for graph: "
           << cur;
        throw LogicException(ss.str());
      }
    }
  } while (!visit.empty());
}

void GraphExtension::checkGraphVariable(TNode g)
{
  if (!g.isVar())
  {
    std::stringstream ss;
    ss << "GraphExtension: Cannot handle graph this is not a variable: " << g;
    throw LogicException(ss.str());
  }
}
void GraphExtension::checkEdge(TNode c)
{
  if (c.getKind() != APPLY_CONSTRUCTOR || c.getNumChildren() != 2
      || !c[0].isConst() || !c[1].isConst())
  {
    std::stringstream ss;
    ss << "GraphExtension: Cannot handle non-constant edge " << c;
    throw LogicException(ss.str());
  }
}

}  // namespace sets
}  // namespace theory
}  // namespace CVC4
