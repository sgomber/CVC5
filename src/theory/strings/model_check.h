/*********************                                                        */
/*! \file model_check.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A model check module for strings.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__MODEL_CHECK_H
#define CVC4__THEORY__STRINGS__MODEL_CHECK_H

#include <map>

#include "expr/node.h"
#include "theory/evaluator.h"

namespace CVC4 {
namespace theory {
namespace strings {

class TheoryStrings;

/** Strings model check
 */
class ModelCheck
{
 public:
  ModelCheck(TheoryStrings& parent);
  ~ModelCheck();
  /** check
   */
  bool check(const std::map<Node, Node>& model);

 private:
  /** The parent who owns this */
  TheoryStrings& d_parent;
  /** An evaluator */
  Evaluator d_eval;
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__MODEL_CHECK_H */
