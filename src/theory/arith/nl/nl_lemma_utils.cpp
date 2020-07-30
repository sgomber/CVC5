/*********************                                                        */
/*! \file nl_lemma_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of utilities for the non-linear solver
 **/

#include "theory/arith/nl/nl_lemma_utils.h"

#include "theory/arith/arith_msum.h"
#include "theory/arith/nl/nl_model.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

LemmaProperty NlLemma::getLemmaProperty() const
{
  return d_preprocess ? LemmaProperty::PREPROCESS : LemmaProperty::NONE;
}

std::ostream& operator<<(std::ostream& out, NlLemma& n)
{
  out << n.d_lemma;
  return out;
}

bool SortNlModel::operator()(Node i, Node j)
{
  int cv = d_nlm->compare(i, j, d_isConcrete, d_isAbsolute);
  if (cv == 0)
  {
    return i < j;
  }
  return d_reverse_order ? cv < 0 : cv > 0;
}

bool SortNonlinearDegree::operator()(Node i, Node j)
{
  unsigned i_count = getDegree(i);
  unsigned j_count = getDegree(j);
  return i_count == j_count ? (i < j) : (i_count < j_count ? true : false);
}

unsigned SortNonlinearDegree::getDegree(Node n) const
{
  std::map<Node, unsigned>::const_iterator it = d_mdegree.find(n);
  Assert(it != d_mdegree.end());
  return it->second;
}

Node ArgTrie::add(Node d, const std::vector<Node>& args)
{
  ArgTrie* at = this;
  for (const Node& a : args)
  {
    at = &(at->d_children[a]);
  }
  if (at->d_data.isNull())
  {
    at->d_data = d;
  }
  return at->d_data;
}

void ConnectedComponents::clear() { d_ufind.clear(); }

void ConnectedComponents::registerConstraint(Node lit)
{
  std::map<Node, Node> msum;
  ArithMSum::getMonomialSumLit(lit, msum);
  Node r;
  bool computedRep = false;
  for (const std::pair<const Node, Node>& m : msum)
  {
    Node t = m.first;
    if (t.isNull())
    {
      // constant, skip
      continue;
    }
    if (r.isNull())
    {
      // use the representative of the first monomial
      r = t;
      continue;
    }
    if (!computedRep)
    {
      // compute the representative when a second monomial is encountered
      r = getRepresentative(r);
      computedRep = true;
    }
    // connect the monomial to the representative
    setRepresentative(r, t);
  }
}

bool ConnectedComponents::areConnected(Node t, Node s)
{
  return getRepresentative(t) == getRepresentative(s);
}

Node ConnectedComponents::getRepresentative(Node t)
{
  std::map<Node, Node>::const_iterator it = d_ufind.find(t);
  if (it != d_ufind.end())
  {
    Node tr = getRepresentative(it->second);
    if (tr != it->second)
    {
      // merge path
      d_ufind[t] = tr;
    }
    return tr;
  }
  return t;
}

void ConnectedComponents::setRepresentative(Node r, Node t)
{
  if (r != t)
  {
    Node tr = getRepresentative(t);
    if (tr != r)
    {
      Assert(d_ufind.find(tr) == d_ufind.end());
      d_ufind[tr] = r;
    }
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
