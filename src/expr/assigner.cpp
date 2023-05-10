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

using namespace cvc5::internal::kind;

namespace cvc5::internal {

Assigner::Assigner(const Node& n) { d_valid = init(n); }

bool Assigner::isValid() const { return d_valid; }

const std::vector<Node>& Assigner::getVariables() const { return d_vars; }

const std::vector<Node>& Assigner::getAssignments(const Node& v) const
{
  std::map<Node, std::vector<Node>>::const_iterator it = d_assignments.find(v);
  Assert(it != d_assignments.end());
  return it->second;
}

const std::vector<Node>& Assigner::getLiterals() const { return d_literals; }

bool Assigner::isAssigner(const Node& n)
{
  std::vector<Node> vars;
  std::map<Node, size_t> varIndex;
  std::map<Node, std::vector<Node>> assignments;
  std::vector<Node> literals;
  return initInternal(n, vars, varIndex, assignments, literals);
}
bool Assigner::init(const Node& n)
{
  return initInternal(n, d_vars, d_varIndex, d_assignments, d_literals);
}
bool Assigner::initInternal(const Node& n,
                            std::vector<Node>& vars,
                            std::map<Node, size_t>& varIndex,
                            std::map<Node, std::vector<Node>>& assignments,
                            std::vector<Node>& literals)
{
  Assert(n.getKind() == OR);
  size_t nargs = n.getNumChildren();
  // split to cubes
  std::vector<std::vector<Node>> cubes;
  cubes.resize(nargs);
  size_t csize = 0;
  for (size_t i = 0; i < nargs; i++)
  {
    const Node& nc = n[i];
    std::vector<Node>& cc = cubes[i];
    Kind nck = nc.getKind();
    if (nck == AND)
    {
      cc.insert(cc.end(), nc.begin(), nc.end());
    }
    else if (nck == EQUAL)
    {
      cc.push_back(nc);
    }
    else
    {
      return false;
    }
    if (i == 0)
    {
      csize = cc.size();
    }
    else if (cc.size() != csize)
    {
      // cube size is not the same for all disjuncts
      return false;
    }
  }
  // infer the variables for the first argument
  Node vtmp;
  Node ctmp;
  for (size_t i = 0; i < nargs; i++)
  {
    std::vector<Node>& cc = cubes[i];
    std::unordered_set<Node> varUsed;
    for (const Node& eq : cc)
    {
      // each literal in the cube must be a variable assignment equality
      if (!isAssignEq(eq, vtmp, ctmp))
      {
        return false;
      }
      if (i == 0)
      {
        // all variables in each cube must be unique
        if (varIndex.find(vtmp) != varIndex.end())
        {
          return false;
        }
        varIndex[vtmp] = vars.size();
        vars.push_back(vtmp);
      }
      else
      {
        // must be a previous variable not used already this iteration
        if (varIndex.find(vtmp) == varIndex.end()
            || varUsed.find(vtmp) != varUsed.end())
        {
          return false;
        }
        varUsed.insert(vtmp);
      }
      assignments[vtmp].push_back(ctmp);
      literals.push_back(eq);
    }
  }
  return true;
}

bool Assigner::isAssignEq(const Node& n, Node& v, Node& c)
{
  if (n.getKind() != EQUAL)
  {
    return false;
  }
  for (size_t i = 0; i < 2; i++)
  {
    if (n[i].isVar() && n[1 - i].isConst())
    {
      v = n[i];
      c = n[1 - i];
      return true;
    }
  }
  return false;
}

AssignerDb::AssignerDb() {}

Assigner* AssignerDb::getAssigner(const Node& n)
{
  std::map<Node, std::unique_ptr<Assigner>>::iterator it = d_db.find(n);
  if (it == d_db.end())
  {
    d_db[n].reset(new Assigner(n));
    Assigner* a = d_db[n].get();
    if (a->isValid())
    {
      return a;
    }
    d_db.erase(n);
    return nullptr;
  }
  return it->second.get();
}

}  // namespace cvc5::internal
