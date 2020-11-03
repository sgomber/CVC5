/*********************                                                        */
/*! \file sygus_qe_preproc.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus quantifier elimination preprocessor
 **/

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_QE_PREPROC_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_QE_PREPROC_H

#include <string>
#include <vector>
#include "expr/node.h"
#include "expr/type.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

class SingleInvocationPartition;

/**
 * Helper substitution class.
 */
class Subs
{
 public:
  bool empty() const;
  size_t size() const;
  bool contains(Node v) const;
  void add(Node v);
  void add(const std::vector<Node>& vs);
  void add(Node v, Node s);
  void add(const std::vector<Node>& vs, const std::vector<Node>& ss);
  void addEquality(Node eq);
  void append(Subs& s);
  void applyToRange(Subs& s);
  void rapplyToRange(Subs& s);
  Node apply(Node n) const;
  Node rapply(Node n) const;
  Node getEquality(size_t i) const;
  std::vector<Node> d_vars;
  std::vector<Node> d_subs;
};

/**
 * This module does quantifier elimination as a preprocess step
 * for "non-ground single invocation synthesis conjectures":
 *   exists f. forall xy. P[ f(x), x, y ]
 * We run quantifier elimination:
 *   exists y. P[ z, x, y ] ----> Q[ z, x ]
 * Where we replace the original conjecture with:
 *   exists f. forall x. Q[ f(x), x ]
 * For more details, see Example 6 of Reynolds et al. SYNT 2017.
 */
class SygusQePreproc
{
 public:
  SygusQePreproc(QuantifiersEngine* qe);
  ~SygusQePreproc() {}
  /**
   * Preprocess. Returns a lemma of the form q = nq where nq is obtained
   * by the quantifier elimination technique outlined above.
   */
  Node preprocess(Node q);

 private:
  /**
   * Eliminate variables
   */
  Node eliminateVariables(Node q,
                          const std::vector<Node>& allf,
                          const std::vector<Node>& maxf,
                          const Subs& xf,
                          Subs& solvedf,
                          SingleInvocationPartition& sip);
  /**
   * Eliminate functions
   */
  Node eliminateFunctions(Node q,
                          const std::vector<Node>& allf,
                          const std::vector<Node>& maxf,
                          const Subs& xf,
                          Subs& solvedf,
                          SingleInvocationPartition& sip);
  /**
   * Decompose conjecture
   */
  void decomposeConjecture(Node q,
                           std::vector<Node>& allf,
                           std::vector<Node>& unsf,
                           Subs& solved);
  /** Get maximal arity functions */
  bool getMaximalArityFuncs(const std::vector<Node>& unsf,
                            std::vector<Node>& maxf,
                            Subs& remf,
                            Subs& xf,
                            std::vector<Node>& xargs);
  /** Extend function arguments */
  bool extendFuncArgs(Node f,
                      const std::vector<Node>& xargs,
                      Subs& remf,
                      Subs& xf);
  /**
   * Make conjecture
   */
  Node mkConjecture(const std::vector<Node>& allf,
                    const Subs& solved,
                    Node conj,
                    Node ipl);
  /** Pointer to quantifiers engine */
  QuantifiersEngine* d_quantEngine;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS__SYGUS_QE_PREPROC_H */
