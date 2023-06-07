/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Plugin
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__PLUGIN_H
#define CVC5__EXPR__PLUGIN_H

#include <vector>

#include "expr/node.h"

namespace cvc5::internal {

/**
 * A plugin.
 */
class Plugin
{
 public:
  /** Construct a plugin. */
  Plugin() {}
  virtual ~Plugin() {}
  /** Check function, returns the empty vector */
  virtual std::vector<Node> check() = 0;
  /** Notify SAT clause */
  virtual void notifySatClause(const Node& lem) = 0;
  /** Notify theory lemma */
  virtual void notifyTheoryLemma(const Node& lem) = 0;
  /** Get name */
  virtual std::string getName() = 0;
  /** Get sharable formula */
  static Node getSharableFormula(const Node& n);
};

}  // namespace cvc5::internal

#endif /*CVC5__EXPR__ORACLE_H*/
