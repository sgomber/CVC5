/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof checker cache utility.
 */

#include "expr/proof_checker_cache.h"

namespace cvc5 {

Node ProofCheckerCache::lookup(PfRule id,
                               const std::vector<Node>& children,
                               const std::vector<Node>& args) const
{
  std::map<PfRule, ProofCheckerCacheTrie>::const_iterator it = d_data.find(id);
  if (it == d_data.end())
  {
    return Node::null();
  }
  std::map<Node, ProofCheckerCacheTrie>::const_iterator itc;
  const ProofCheckerCacheTrie* pcct = &it->second;
  for (const Node& c : children)
  {
    itc = pcct->d_children.find(c);
    if (itc == pcct->d_children.end())
    {
      return Node::null();
    }
    pcct = &itc->second;
  }
  Node nullNode;
  itc = pcct->d_children.find(nullNode);
  if (itc == pcct->d_children.end())
  {
    return Node::null();
  }
  pcct = &itc->second;
  for (const Node& a : args)
  {
    itc = pcct->d_children.find(a);
    if (itc == pcct->d_children.end())
    {
      return Node::null();
    }
    pcct = &itc->second;
  }
  return pcct->d_res;
}

void ProofCheckerCache::store(PfRule id,
                              const std::vector<Node>& children,
                              const std::vector<Node>& args,
                              Node res)
{
  ProofCheckerCacheTrie* pcct = &d_data[id];
  for (const Node& c : children)
  {
    pcct = &pcct->d_children[c];
  }
  Node nullNode;
  pcct = &pcct->d_children[nullNode];
  for (const Node& a : args)
  {
    pcct = &pcct->d_children[a];
  }
  pcct->d_res = res;
}

}  // namespace cvc5
