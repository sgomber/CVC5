/*********************                                                        */
/*! \file sygus_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief generic sygus utilities
 **/

#include "theory/quantifiers/sygus/sygus_utils.h"

#include "theory/quantifiers/quantifiers_attributes.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Node mkSygusConjecture(const std::vector<Node>& fs,
                       Node conj,
                       const std::vector<Node>& iattrs)
{
  Assert(!fs.empty());
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> ipls;
  SygusAttribute ca;
  Node sygusVar = nm->mkSkolem("sygus", nm->booleanType());
  sygusVar.setAttribute(ca, true);
  Node instAttr = nm->mkNode(INST_ATTRIBUTE, sygusVar);
  ipls.push_back(instAttr);
  // insert the remaining instantiation attributes
  ipls.insert(ipls.end(), iattrs.begin(), iattrs.end());
  Node ipl = nm->mkNode(INST_PATTERN_LIST, ipls);
  Node bvl = nm->mkNode(BOUND_VAR_LIST, fs);
  return nm->mkNode(FORALL, bvl, conj, ipl);
}

Node mkSygusConjecture(const std::vector<Node>& fs, Node conj)
{
  std::vector<Node> iattrs;
  return mkSygusConjecture(fs, conj, iattrs);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
