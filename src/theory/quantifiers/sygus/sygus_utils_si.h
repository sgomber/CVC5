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

class SygusSiUtils
{
 public:
  /**
   * Returns true if fs is a set of functions that each have the same type.
   */
  static bool areSameType(const std::vector<Node>& fs);
  /**
   * Is the conjecture conj single invocation? This does not do any rewriting
   * to the conjecture or advanced techniques. This method assumes that fs
   * each have the same type.
   *
   * @param fs The set of functions-to-synthesize this check is relative to
   * @param conj The conjecture
   * @param ffs The subset of fs that appears freely in conj
   * @param args The arguments such that all occurrences of fs are applied to
   * exactly this list.
   * @param reqBoundVar Whether we require that fs be applied to bound variables
   * only.
   * @return true if conj is single invocation
   */
  static bool isSingleInvocation(const std::vector<Node>& fs,
                                 Node conj,
                                 std::map<Node, Node>& ffs,
                                 std::vector<Node>& args,
                                 bool reqBoundVar = true);
  static bool isSingleInvocation(const std::vector<Node>& fs,
                                 Node conj,
                                 std::vector<Node>& args,
                                 bool reqBoundVar = true);
  /**
   * Same as above, but where functions are allowed to take different arguments.
   * Functions that are applied to multiple arguments have an empty range.
   * @param fs The set of functions-to-synthesize this check is relative to
   * @param conj The conjecture
   * @param args Mapping whose domain is a subset of fs and range for f are the
   * arguments f is applied to in conj. This is empty if f is applied to
   * multiple arguments
   * @param reqBoundVar Whether we require that fs be applied to bound variables
   * only.
   * @param reqAllValid Whether we abort and return false if there are any
   * functions that are applied to multiple arguments.
   * @param true if reqAllValid is false, or if reqVal is true and all functions
   * in fs are applied to at most one vector of arguments.
   */

  static bool getSingleInvocations(const std::vector<Node>& fs,
                                   Node conj,
                                   std::map<Node, std::vector<Node>>& args,
                                   bool reqBoundVar = true,
                                   bool reqAllValid = true);
  /**
   * Partition the conjecture conj based on the functions-to-synthesize fs.
   * Sets cc and nc such that conj is equivalent to (and cc nc), cc contains
   * fs and nc does not.
   */
  static void partitionConjecture(const std::vector<Node>& fs,
                                  Node conj,
                                  Node& cc,
                                  Node& nc);
  /**
   *
   * Coerce single invocation.
   *
   * @param fs The functions to synthesize
   * @param conj The negated conjecture body
   * @param args The mapping from fs to the arguments they are applied to in
   * conj.
   * @return  a negated conjecture body that is equivalent to conj that is
   * "typed single invocation", or the null node if no such conjecture body can
   * be inferred. We say a conjecture is typed single invocation if there exists
   * a function f in fs such that args[g] is a subset of args[f] for each g.
   */
  static Node coerceSingleInvocation(const std::vector<Node>& fs,
                                     Node conj,
                                     std::map<Node, std::vector<Node>>& args);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_UTILS_SI_H */
