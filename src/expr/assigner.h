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
 * An assigner
 */

#include "cvc5_public.h"

#ifndef CVC5__ASSIGNER_H
#define CVC5__ASSIGNER_H

#include <iosfwd>
#include <memory>

#include "expr/node.h"

namespace cvc5::internal {

class Assigner
{
 public:
  /** */
  Assigner(const Node& n);
  ~Assigner() {}
  bool isValid() const;
  const std::vector<Node>& getVariables() const;
  const std::vector<Node>& getAssignments(const Node& v) const;
  const std::vector<Node>& getLiterals() const;
 private:
  bool init(const Node& n);
  bool isAssignEq(const Node& n, Node& v, Node& c);
  bool isCube(const Node& n);
  bool d_valid;
  std::vector<Node> d_vars;
  std::map<Node, size_t> d_varIndex;
  std::map<Node, std::vector<Node>> d_assignments;
  std::vector<Node> d_literals;
};

class AssignerDb
{
 public:
  AssignerDb();
  ~AssignerDb() {}
  Assigner* getAssigner(const Node& n);
 private:
  std::map<Node, std::unique_ptr<Assigner>> d_db;
};

}  // namespace cvc5::internal

#endif /* CVC5__ASSIGNER_H */
