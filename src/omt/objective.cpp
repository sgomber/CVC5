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
#include "omt/objective.h"

namespace cvc5::internal {
namespace omt {

Objective::Objective(ObjectiveKind k, const Node& term) : d_kind(k), d_term(term) {}
Objective::Objective(ObjectiveKind k, const std::vector<std::shared_ptr<Objective>>& children) : d_kind(k), d_children(children) {}

ObjectiveKind Objective::getKind() const { return d_kind; }
const Node& Objective::getTerm() const { return d_term; }
size_t Objective::getNumChildren() const { return d_children.size(); }
const Objective& Objective::getChild(size_t i) const { return *d_children[i].get(); }

}
}  // namespace cvc5::internal

