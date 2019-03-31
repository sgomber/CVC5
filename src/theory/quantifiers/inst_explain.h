/*********************                                                        */
/*! \file inst_explain.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Instantiate explain utility
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_H
#define __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_H

#include <map>
#include <vector>
#include "expr/node.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class InstExplainLit
{
 public:
   InstExplainLit(){}
  /** initialize */
  void initialize(Node inst);
  /** reset */
  void reset();
  /** add inst explanation */
  void addInstExplanation(Node inst);
  /** add propagating instantiation */
  void setPropagating(Node inst);
  /** the list of possible instantiation lemmas that may propagate this literal */
  std::vector< Node > d_insts;
  /** the list of instantiation lemmas that actually currently propagate this literal */
  std::vector< Node > d_curr_prop_insts;
private:
  /** the literal this object is for */
  Node d_this;
};

class InstExplainDb;

class InstExplainInst
{
public:
  /** initialize */
  void initialize(Node inst);
  /** propagate */
  void propagate( QuantifiersEngine * qe, std::vector< Node >& lits );
private:
  /** the instantiation lemma */
  Node d_this;
  /** evaluate */
  bool evaluate( Node n, std::map< Node, bool >& ecache, QuantifiersEngine * qe );
};


}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_H */
