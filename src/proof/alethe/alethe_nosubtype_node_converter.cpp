/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Alethe node conversion to remove subtyping
 */

#include "proof/alethe/alethe_nosubtype_node_converter.h"

namespace cvc5::internal {
namespace proof {

Node AletheNoSubtypeNodeConverter::postConvert(Node n)
{
  return n;
}

}  // namespace proof
}  // namespace cvc5::internal
