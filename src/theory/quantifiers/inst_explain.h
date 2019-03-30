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
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {


class InstExplain
{
public:
  std::vector< Node > d_insts;
};

class EqExplainer
{
public:
  EqExplainer(){}
  virtual ~EqExplainer(){}
  virtual bool explain(Node lit, std::vector<TNode>& assumptions) = 0;
};

class EqualityExplainerEe : public EqExplainer
{
public:
  EqualityExplainerEe() : d_ee(nullptr){}
  virtual ~EqualityExplainerEe(){}
  /** the equality engine */
  eq::EqualityEngine * d_ee;
  /** explain */
  bool explain(Node lit, std::vector<TNode>& assumptions) override;
};

class InstExplainDb
{
public:
  InstExplainDb();
  /** register explanations */
  void registerExplanation(Node ilem, Node n);
  /** get instantiation explain */
  InstExplain& getInstExplain( Node lit );
  /** explain */
  void explain( std::vector< Node >& exp, EqExplainer * eqe, const char * ctx );
private:
  /** common constants */
  Node d_false;
  /** map from literal to possible explanations */
  std::map< Node, InstExplain > d_lit_explains;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H */
