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
    // can be (c1, c2) in g or (c1, c2) in tclosure(g)
    TNode g = node[1];
    bool isPath = (g.getKind() == TCLOSURE);
    g = isPath ? g[0] : g;
    GraphInfo& gi = getGraphInfo(g);
    gi.addEdgeAtom(node, isPath);
  }
  else if (k == SUBSET)
  {
    TNode g = node[0];
    GraphInfo& gi = getGraphInfo(g);
    gi.addSubsetRestriction(node);
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
  std::stringstream ss;
  ss << "GraphExtension::check not implemented yet";
  throw LogicException(ss.str());
}

void GraphExtension::collectModelInfo(TheoryModel* m)
{
  
}

GraphInfo& GraphExtension::getGraphInfo(TNode g)
{
  std::map<TNode, GraphInfo>::iterator it = d_ginfo.find(g);
  if (it == d_ginfo.end())
    ;
  {
    GraphInfo& gi = d_ginfo[g];
    gi.initialize(g);
    return gi;
  }
  return it->second;
}

}  // namespace sets
}  // namespace theory
}  // namespace CVC4
