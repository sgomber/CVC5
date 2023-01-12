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
 * Objective class.
 */

#ifndef CVC5__OMT__OBJECTIVE_H
#define CVC5__OMT__OBJECTIVE_H

#include <memory>
#include <vector>

#include "api/cpp/cvc5_types.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace omt {

/**
 */
class Objective
{
 public:
  Objective(ObjectiveKind k, const Node& term);
  Objective(ObjectiveKind k,
            const std::vector<std::shared_ptr<Objective>>& children);
  virtual ~Objective() {}

  ObjectiveKind getKind() const;
  const Node& getTerm() const;
  size_t getNumChildren() const;
  const Objective& getChild(size_t i) const;

 private:
  ObjectiveKind d_kind;
  Node d_term;
  std::vector<std::shared_ptr<Objective>> d_children;
};

}  // namespace omt
}  // namespace cvc5::internal

#endif
