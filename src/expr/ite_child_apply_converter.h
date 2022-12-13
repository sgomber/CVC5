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

/**
 */
class IteChildApplyConverter
{
 public:
  IteChildApplyConverter(const Node& t, const Node& var);
  ~IteChildApplyConverter() {}
  /** convert node n as described above during post-order traversal */
  Node postConvertUntyped(Node orig,
                                  const std::vector<Node>& terms,
                                  bool termsChanged) override;
private:
  /** Should we traverse n? */
  bool shouldTraverse(Node n) override;
  /** The term */
  Node d_term;
  /** The variable */
  TNode d_var;
};

}  // namespace cvc5::internal

#endif
