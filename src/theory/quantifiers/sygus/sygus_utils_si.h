/*********************                                                        */
/*! \file sygus_utils_si.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus utilities for single invocation
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_UTILS_SI_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_UTILS_SI_H

#include <map>
#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * Returns true if fs is a set of functions that we could apply single
 * invocation techniques for
 */
bool isSingleInvocationType(const std::vector<Node>& fs);
/**
 * Is the conjecture conj single invocation? This does not do any rewriting
 * to the conjecture or advanced techniques.
 *
 * @param fs The set of functions-to-synthesize this check is relative to
 * @param conj The conjecture
 * @param ffs The subset of fs that appears freely in conj
 * @param args The arguments such that all occurrences of fs are applied to
 * exactly this list.
 * @return true if conj is single invocation
 */
bool isSingleInvocation(const std::vector<Node>& fs,
                        Node conj,
                        std::map<Node, Node>& ffs,
                        std::vector<Node>& args);
bool isSingleInvocation(const std::vector<Node>& fs,
                        Node conj,
                        std::vector<Node>& args);
/**
 * Same as above, but where functions are allowed to take different arguments.
 * @param fs The set of functions-to-synthesize this check is relative to
 * @param conj The conjecture
 * @param args Mapping whose domain is a subset of fs and range for f are the
 * arguments f is applied to in conj, if any.
 * @return true if conj is single invocation
 */

bool isSingleInvocation(const std::vector<Node>& fs,
                        Node conj,
                        std::map<Node, std::vector<Node>>& args);

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_UTILS_SI_H */
