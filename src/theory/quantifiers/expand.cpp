/*********************                                                        */
/*! \file expand.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of expand
 **/

#include "theory/quantifiers/expand.h"

#include "theory/rep_set.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/quantifiers_attributes.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Node Expand::expand( Node q )
{
  Trace("qexpand") << "Expand quantified formula " << q << "?" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  // try to initialize the representative set for each type
  RepSet rs;
  for (unsigned i = 0, size = q[0].getNumChildren(); i < size; i++)
  {
    TypeNode tn = q[0][i].getType();
    uint32_t maxCard = std::numeric_limits<uint32_t>::max();
    if (!TermEnumeration::mayComplete(tn, maxCard))
    {
      Trace("qexpand")
          << "...cannot expand type " << tn << "." << std::endl;
      return Node::null();
    }
    else
    {
      rs.complete(tn);
    }
  }
  std::vector<Node> conj;
  std::vector<Node> vars;
  for (const Node& v : q[0])
  {
    vars.push_back(v);
  }
  RepSetIterator riter(&rs);
  if (riter.setQuantifier(q))
  {
    std::vector<Node> subs;
    while (!riter.isFinished())
    {
      subs.clear();
      riter.getCurrentTerms(subs);
      Node inst =
          q[1].substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      conj.push_back(inst);
      riter.increment();
    }
  }
  else
  {
    Trace("qexpand") << "...failed to initialize quantifier." << std::endl;
    return Node::null();
  }
  Node ret = nm->mkNode(AND, conj);
  Trace("qexpand") << "...got " << ret << std::endl;
  return ret;
}
  
QuantifierExpander::QuantifierExpander( QuantifiersEngine * qe ) : QuantifiersReducer(qe) {

}

bool QuantifierExpander::shouldReduce(Node q)
{
  return d_quantEngine->getQuantAttributes()->isQuantExpand(q);
}

void QuantifierExpander::doReduce( Node q )
{
  Node exq = Expand::expand( q );
  Node rlem = q.eqNode(exq);
  Trace("quant-expand") << "QuantifiersExpander: reduce: " << rlem << std::endl;
  d_quantEngine->addLemma(rlem);
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
