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

#include "expr/assigner.h"

namespace cvc5::internal {

Assigner::Assigner(const Node& n) {}
~Assigner() {}
bool Assigner::isValid() const { return d_valid; }
const std::vector<Node>& Assigner::getVariables() const { return d_vars; }
const std::vector<std::vector<Node>>& Assigner::getAssignments() const { return d_assignments; }
const std::vector<Node>& Assigner::getLiterals() const { return d_literals; }

AssignerDb::AssignerDb(){}

bool AssignerDb::registerToDb(const Node& n)
{
  std::map<Node, std::unique_ptr<Assigner>>::iterator it = d_db.find(n);
  if (it==d_db.end())
  {
    d_db[n].init(n);
    d_db[n].reset(
        new Assigner(n));
    return d_db[n]->isValid();
  }
  return it->second->isValid();
}

const Assigner* AssignerDb::getAssigner() const
{
  std::map<Node, std::unique_ptr<Assigner>>::const_iterator it = d_db.find(n);
  Assert (it!=d_db.end());
  return it->second.get();
}


}  // namespace cvc5::internal

