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

#ifndef CVC5__SMT__SMT_DRIVER_ABSTRACT_REFINE_H
#define CVC5__SMT__SMT_DRIVER_ABSTRACT_REFINE_H

#include "smt/smt_driver.h"
#include "util/result.h"
#include "expr/subs.h"

namespace cvc5::internal {
namespace smt {

class SmtSolver;
class ContextManager;

/**
 * An SMT driver that is based on abstraction refinement
 */
class SmtDriverAbstractRefine : public SmtDriver
{
 public:
  SmtDriverAbstractRefine(Env& env, SmtSolver& smt, ContextManager* ctx);
  virtual ~SmtDriverAbstractRefine() {}

 protected:
  Result checkSatNext(preprocessing::AssertionPipeline& ap) override;
  void getNextAssertions(preprocessing::AssertionPipeline& ap) override;

 private:
  /** return the Boolean abstraction of n */
  Node booleanAbstractionOf(const Node& n);
  /** check model */
  bool checkModel();
  /** get abstraction variable for */
  Node getAbstractionVariableFor(const Node& n);
  /** Initialized */
  bool d_initialized;
  /** The assertions */
  std::vector<Node> d_currAssertions;
  /** Mapping terms to abstraction variables */
  std::map<Node, Node> d_termToAVar;
  /** Reverse of above */
  std::map<Node, Node> d_avarToTerm;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
