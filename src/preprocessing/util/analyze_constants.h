/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Analyzing constants
 */
#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__UTIL__ANALYZE_CONSTANTS_H
#define CVC5__PREPROCESSING__UTIL__ANALYZE_CONSTANTS_H

#include "expr/node.h"
#include "theory/quantifiers/sygus/sygus_enumerator_callback.h"
#include "expr/subs.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

class SygusEnumeratorCallbackConstElim : public theory::quantifiers::SygusEnumeratorCallback
{
public:
  SygusEnumeratorCallbackConstElim(Node e, const std::vector<Node>& cs);
  /**
   * Add term, return true if the term should be considered in the enumeration
   */
  bool addTerm(Node bn, Node bnr, bool isPre) override;
private:
  /** Map from constants to solved form */
  std::map<Node, Node> d_solved;
  /** Substitution */
  Subs d_subs;
};
  
/**
 * Analyze
 */
class AnalyzeConstants
{
 public:
  AnalyzeConstants();

  /** Analyze constants */
  void analyzeConstants(TypeNode tn, const std::vector<Node>& cs);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5

#endif /* CVC5__PREPROCESSING__UTIL__ANALYZE_CONSTANTS_H */
