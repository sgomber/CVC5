/*********************                                                        */
/*! \file gen_lit_info.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Generalized literal info
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__GEN_LIT_INFO_H
#define __CVC4__THEORY__QUANTIFIERS__GEN_LIT_INFO_H

#include <map>
#include <vector>
#include "expr/node.h"
#include "theory/quantifiers/inst_explain.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** generalized literal information
 *
 * This stores the state of a generalized literal.
 */
class GLitInfo
{
 public:
  GLitInfo() : d_iei(nullptr) {}
  InstExplainInst* d_iei;
  std::map<TNode, Node> d_subs_modify;
  /** required assumptions
   */
  std::vector< Node > d_assumptions;
  /** initialize this information */
  void initialize(InstExplainInst* iei);
  /** initialize to the result of merging the generalizations of a and b
   *
   * It should be the case that ( a * subs(ga.d_iei) ) = ( b * subs(gb.d_iei) ).
   *
   * For example:
   */
  bool initialize(TNode a, const GLitInfo& ga, TNode b, const GLitInfo& gb);
  
  
  bool merge(TNode a, TNode b, const GLitInfo& gb);
  bool checkCompatible(TNode a, TNode b, const GLitInfo& gb);
  
  bool drop(TNode b);
private:
  bool mergeInternal(TNode a, TNode b, const GLitInfo& gb, bool allowBind);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__GEN_LIT_INFO_H */
