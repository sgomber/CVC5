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
#include "cvc5_private.h"

#ifndef CVC4__PROOF__EXPR__ITE_CHILD_APPLY_CONVERTER_H
#define CVC4__PROOF__EXPR__ITE_CHILD_APPLY_CONVERTER_H

#include "expr/node.h"
#include "expr/node_converter.h"

namespace cvc5::internal {

IteChildApplyConverter::IteChildApplyConverter(const Node& t, const Node& var) : d_term(t), d_var(var){}

Node IteChildApplyConverter::postConvertUntyped(Node orig,
                                const std::vector<Node>& terms,
                                bool termsChanged)
{
  if (orig.getKind()==ITE)
  {
    std::vector<Node> children;
    children.push_back(terms[0]);
    for (size_t i=0; i<2; i++)
    {
      if (terms[i].getKind()==ITE)
      {
        // take conversion
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
    return NodeManager::currentNM()->mkNode(ITE, children);
  }
  // otherwise return original
  return orig;
}

bool IteChildApplyConverter::shouldTraverse(Node n)
{
  return n.getKind()==ITE;
}


}  // namespace cvc5::internal

#endif
