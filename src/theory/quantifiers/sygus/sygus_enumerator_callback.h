/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * sygus_enumerator
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_ENUMERATOR_CALLBACK_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_ENUMERATOR_CALLBACK_H

#include <unordered_set>

#include "expr/node.h"
#include "theory/quantifiers/extended_rewrite.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
  
  class ExampleEvalCache;
  class SygusStatistics;
  class SygusSampler;

class SygusEnumeratorCallback
{
 public:
  SygusEnumeratorCallback(Node e, ExampleEvalCache* eec = nullptr,
                  SygusStatistics* s = nullptr, SygusSampler* ssrv = nullptr);
  virtual ~SygusEnumeratorCallback(){}
  /** Add term, return true if successful */
  virtual bool addTerm(Node n);

 private:
  /** The enumerator */
  Node d_enum;
  /** The type of enum */
  TypeNode d_tn;
  /**
   * Pointer to the example evaluation cache utility (used for symmetry
   * breaking).
   */
  ExampleEvalCache* d_eec;
  /** pointer to the statistics */
  SygusStatistics* d_stats;
  /** sampler (for --sygus-rr-verify) */
  SygusSampler* d_samplerRrV;
  /** extended rewriter */
  ExtendedRewriter d_extr;
  /** the set of builtin terms corresponding to the above list */
  std::unordered_set<Node> d_bterms;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS_ENUMERATOR_CALLBACK_H */
