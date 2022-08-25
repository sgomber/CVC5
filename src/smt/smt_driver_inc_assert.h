/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for SMT queries in an SolverEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__SMT_DRIVER_INC_ASSERT_H
#define CVC5__SMT__SMT_DRIVER_INC_ASSERT_H

#include "smt/smt_driver.h"
#include "util/result.h"

namespace cvc5::internal {
namespace smt {

class SmtSolver;
class ContextManager;

class SmtDriverIncAssert : public SmtDriver
{
 public:
  SmtDriverIncAssert(Env& env, SmtSolver& smt, ContextManager* ctx);

 protected:
  Result checkSatNext(bool& checkAgain) override;
  void getNextAssertions(Assertions& as) override;

 private:
  /**
   * Record current model, return true if we set d_nextIndexToInclude, 
   * indicating that we want to include a new assertion.
   * 
   * @param allAssertsSat set to true if the current model satisfies all
   * assertions.
   */
  bool recordCurrentModel(bool& allAssertsSat);
  /** Common nodes */
  Node d_true;
  Node d_false;
  /** Initialized */
  bool d_initialized;
  /** The original preprocessed assertions */
  std::vector<Node> d_ppAsserts;
  /** The original skolem map */
  std::unordered_map<size_t, Node> d_ppSkolemMap;
  /** the model value map */
  std::vector<std::vector<Node>> d_modelValues;
  /** set of model indices that only had unknown points */
  std::unordered_set<size_t> d_unkModels;
  /** next index to include */
  size_t d_nextIndexToInclude;
  /**
   * All information about an assertion.
   */
  class AssertInfo
  {
   public:
    /** List of models that we are covering (false) */
    std::vector<size_t> d_cover;
    /** List of models that we are covering (unknown) */
    std::vector<size_t> d_coverUnk;
    /** the skolem */
    Node d_skolem;
  };
  /** The current indices in d_ppAsserts we are considering */
  std::map<size_t, AssertInfo> d_ainfo;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
