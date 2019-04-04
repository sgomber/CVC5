/*********************                                                        */
/*! \file equality_explain.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Equality explain utility
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__EQUALITY_EXPLAIN_H
#define __CVC4__THEORY__QUANTIFIERS__EQUALITY_EXPLAIN_H

#include <map>
#include <vector>
#include "expr/node.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class EqExplainer
{
 public:
  EqExplainer() {}
  virtual ~EqExplainer() {}
  virtual bool explain(Node lit,
                       std::vector<TNode>& assumptions,
                       eq::EqProof* eqp = nullptr) = 0;

 protected:
  bool explainEe(eq::EqualityEngine* ee,
                 Node lit,
                 std::vector<TNode>& assumptions,
                 eq::EqProof* eqp);
};

class EqExplainerEe : public EqExplainer
{
 public:
  EqExplainerEe(eq::EqualityEngine* ee) : d_ee(ee) {}
  virtual ~EqExplainerEe() {}
  /** explain */
  bool explain(Node lit,
               std::vector<TNode>& assumptions,
               eq::EqProof* eqp = nullptr) override;

 private:
  /** the equality engine */
  eq::EqualityEngine* d_ee;
};

class EqExplainerTe : public EqExplainer
{
 public:
  EqExplainerTe(TheoryEngine* te) : d_te(te) {}
  virtual ~EqExplainerTe() {}
  /** explain */
  bool explain(Node lit,
               std::vector<TNode>& assumptions,
               eq::EqProof* eqp = nullptr) override;

 private:
  /** the theory engine */
  TheoryEngine* d_te;
};


}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__EQUALITY_EXPLAIN_H */
