/*********************                                                        */
/*! \file si_infer.h
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

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS__SI_INFER_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS__SI_INFER_H

#include <map>
#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SingleInvocationInference
{
 public:
  /**
   * Coerce single invocation.
   *
   * @param fs The functions to synthesize
   * @param conj The negated conjecture body
   * @param allSiVars All single invocation variables
   * @param maxf The maximal arity functions among those in fs
   * @param args The mapping from fs to the arguments they are applied to in
   * conj.
   * @return a negated conjecture body that is equivalent to conj that is
   * "typed single invocation", or the null node if no such conjecture body can
   * be inferred. We say a conjecture is typed single invocation if there exists
   * a function f in fs such that args[g] is a subset of args[f] for each g.
   */
  static Node coerceSingleInvocation(const std::vector<Node>& fs,
                                     Node conj,
                                     std::vector<Node>& allSiVars,
                                     std::vector<Node>& maxf,
                                     std::map<Node, std::vector<Node>>& args);

 private:
  /**
   * Same as above, but without resorting to reasoning across conjunctions.
   */
  static Node coerceSingleInvocationSimple(
      const std::vector<Node>& fs,
      Node conj,
      std::vector<Node>& allSiVars,
      std::vector<Node>& maxf,
      std::map<Node, std::vector<Node>>& args);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS__SI_INFER_H */
