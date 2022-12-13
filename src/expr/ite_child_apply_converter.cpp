/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of annotation elimination node conversion
 */

#include "expr/ite_child_apply_converter.h"

namespace cvc5::internal {

IteChildApplyConverter::IteChildApplyConverter(theory::Rewriter& rew, const Node& t, const Node& var) : d_rew(rew), d_term(t), d_var(var){}

Node IteChildApplyConverter::postConvertUntyped(Node orig,
                                const std::vector<Node>& terms,
                                bool termsChanged)
{
  if (orig.getKind()==kind::ITE)
  {
    std::vector<Node> children;
    children.push_back(terms[0]);
    for (size_t i=1; i<=2; i++)
    {
      if (orig[i].getKind()==kind::ITE)
      {
        // take conversion if not a leaf
        children.push_back(terms[i]);
      }
      else
      {
        // apply to leaves
        TNode t = terms[i];
        Node ts = d_term.substitute(d_var, t);
        children.push_back(ts);
      }
    }
    Node ret = NodeManager::currentNM()->mkNode(kind::ITE, children);
    return d_rew.rewrite(ret);
  }
  // otherwise return original
  return orig;
}

bool IteChildApplyConverter::shouldTraverse(Node n)
{
  return n.getKind()==kind::ITE;
}

}  // namespace cvc5::internal

