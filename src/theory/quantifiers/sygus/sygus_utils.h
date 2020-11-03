/*********************                                                        */
/*! \file sygus_utils.h
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

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_UTILS_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_UTILS_H

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * Make (negated) sygus conjecture of the form
 *   forall fs. conj
 * with instantiation attributes in ips. Notice that the marker for
 * sygus conjecture is automatically prepended to this list.
 */
Node mkSygusConjecture(const std::vector<Node>& fs,
                       Node conj,
                       const std::vector<Node>& iattrs);
/** Same as above, without auxiliary instantiation attributes */
Node mkSygusConjecture(const std::vector<Node>& fs, Node conj);

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_UTILS_H */
