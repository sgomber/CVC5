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

/**
 * An abstract class for explaining ground equality literals.
 */
class EqExplainer
{
 public:
  EqExplainer() {}
  virtual ~EqExplainer() {}
  /**
   * If this method returns true, then assumptions is updated with a set of
   * literals that are asserted in the current SAT context that entail lit.
   *
   * If eqp is non-null, then it is populated with a proof of lit from
   * assumptions. The format of this proof is the same as proofs generated
   * by the equality engine (uf/equality_engine.h/cpp).
   */
  virtual bool explain(Node lit,
                       std::vector<TNode>& assumptions,
                       eq::EqProof* eqp = nullptr) = 0;

 protected:
  /**
   * Explain with equality engine ee.
   * This method returns true if lit can be explained by the equality engine
   * ee, or has a trivial explanation. If so, we add literals to assumptions
   * that entail lit and update eqp to a proof of lit from assumptions.
   */
  bool explainEe(eq::EqualityEngine* ee,
                 Node lit,
                 std::vector<TNode>& assumptions,
                 eq::EqProof* eqp);
};

/** A basic equality explainer that uses a pointer to an equality engine */
class EqExplainerEe : public EqExplainer
{
 public:
  EqExplainerEe(eq::EqualityEngine* ee) : d_ee(ee) {}
  virtual ~EqExplainerEe() {}
  /** explain using the equality engine of this class */
  bool explain(Node lit,
               std::vector<TNode>& assumptions,
               eq::EqProof* eqp = nullptr) override;

 private:
  /** the equality engine of this class */
  eq::EqualityEngine* d_ee;
};

/**
 * An equality explainer based on a pointer to a theory engine.
 *
 * This class attempts to find a theory that has an equality engine that can
 * explain given literals. This is inherently incomplete (by design) since
 * some equalities do not have explanations justified by equality engines,
 * e.g. in theory of arithmetic.
 */
class EqExplainerTe : public EqExplainer
{
 public:
  EqExplainerTe(TheoryEngine* te) : d_te(te) {}
  virtual ~EqExplainerTe() {}
  /** explain using the theory engine of this class */
  bool explain(Node lit,
               std::vector<TNode>& assumptions,
               eq::EqProof* eqp = nullptr) override;

 private:
  /** the theory engine of this class */
  TheoryEngine* d_te;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__EQUALITY_EXPLAIN_H */
