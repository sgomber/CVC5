/*********************                                                        */
/*! \file datatypes_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriter for the theory of (co)inductive datatypes
 **
 ** Rewriter for the theory of (co)inductive datatypes.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__DATATYPES__DATATYPES_REWRITER_H
#define CVC4__THEORY__DATATYPES__DATATYPES_REWRITER_H

#include "expr/node_manager_attributes.h"
#include "theory/theory_rewriter.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

class DatatypesRewriter : public TheoryRewriter
{
 public:
  RewriteResponse postRewrite(TNode in) override;
  RewriteResponse preRewrite(TNode in) override;

 private:
  /** rewrite constructor term in */
  static RewriteResponse rewriteConstructor(TNode in);
  /** rewrite selector term in */
  static RewriteResponse rewriteSelector(TNode in);
  /** rewrite tester term in */
  static RewriteResponse rewriteTester(TNode in);
}; /* class DatatypesRewriter */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__DATATYPES__DATATYPES_REWRITER_H */
