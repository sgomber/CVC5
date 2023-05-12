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

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

Assigner::Assigner(const Node& n) : d_node(n)
{
  d_valid = init(n);
  Assert(d_valid);
  d_satLiteral = getSatLiteral(n);
}

const Node& Assigner::getNode() const { return d_node; }

const Node& Assigner::getSatLiteral() const { return d_satLiteral; }

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
  std::map<Node, std::vector<Node>> assignments;
  std::vector<Node> literals;
  return initInternal(n, vars, assignments, literals);
}

Node Assigner::getSatLiteral(const Node& n)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* skm = nm->getSkolemManager();
  return skm->mkSkolemFunction(SkolemFunId::ASSIGNER, nm->booleanType(), n);
}

bool Assigner::init(const Node& n)
{
  return initInternal(n, d_vars, d_assignments, d_literals);
}

bool Assigner::isLiteralCube(const Node& n, std::vector<Node>& cc)
{
  Kind nck = n.getKind();
  if (nck == AND)
  {
    cc.insert(cc.end(), n.begin(), n.end());
  }
  else
  {
    cc.push_back(n);
  }
  // each cube must be conjunction of theory literals
  for (const Node& lit : cc)
  {
    TNode atom = lit.getKind() == NOT ? lit[0] : lit;
    if (!expr::isTheoryAtom(atom))
    {
      return false;
    }
  }
  return true;
}
bool Assigner::isLiteralCube(const Node& n)
{
  std::vector<Node> cc;
  return isLiteralCube(n, cc);
}

bool Assigner::initInternal(const Node& n,
                            std::vector<Node>& vars,
                            std::map<Node, std::vector<Node>>& assignments,
                            std::vector<Node>& literals)
{
  if (n.getKind() != OR)
  {
    return false;
  }
  size_t nargs = n.getNumChildren();
  // split to cubes
  std::vector<std::vector<Node>> cubes;
  cubes.resize(nargs);
  for (size_t i = 0; i < nargs; i++)
  {
    const Node& nc = n[i];
    std::vector<Node>& cc = cubes[i];
    if (!isLiteralCube(nc, cc))
    {
      Trace("assigner-init") << "Not atom " << nc << std::endl;
      Trace("assigner-init") << "...from " << n << std::endl;
      return false;
    }
  }
  // infer the variables for the first argument
  Node vtmp;
  Node ctmp;
  for (size_t i = 0; i < nargs; i++)
  {
    std::vector<Node>& cc = cubes[i];
    for (const Node& lit : cc)
    {
      // Check if the literal in the cube is a variable assignment equality.
      // If so, then we push to the end of assigns (if we haven't already
      // found a conflicting assignment).
      if (isAssignEq(lit, vtmp, ctmp))
      {
        std::vector<Node>& assigns = assignments[vtmp];
        if (assigns.size() <= i)
        {
          assigns.resize(i);
          assigns.push_back(ctmp);
        }
      }
    }
    literals.insert(literals.end(), cc.begin(), cc.end());
  }
  // ensure all assignments are resized
  for (std::pair<const Node, std::vector<Node>>& as : assignments)
  {
    as.second.resize(nargs);
    // save the list of assigned variables
    vars.push_back(as.first);
  }
  return true;
}

bool Assigner::isAssignEq(const Node& n, Node& v, Node& c)
{
  Kind k = n.getKind();
  if (k == EQUAL)
  {
    for (size_t i = 0; i < 2; i++)
    {
      if (n[i].isVar() && n[1 - i].isConst())
      {
        v = n[i];
        c = n[1 - i];
        return true;
      }
    }
  }
  return false;
}

AssignerDb::AssignerDb() {}

Assigner* AssignerDb::registerAssigner(const Node& n)
{
  std::map<Node, std::unique_ptr<Assigner>>::iterator it = d_db.find(n);
  if (it == d_db.end())
  {
    d_db[n].reset(new Assigner(n));
    Assigner* a = d_db[n].get();
    if (a->isValid())
    {
      registerLitsForAssigner(n, a);
      return a;
    }
    d_db.erase(n);
    return nullptr;
  }
  return it->second.get();
}

void AssignerDb::registerLitsForAssigner(const Node& n, Assigner* a)
{
  const std::vector<Node>& lits = a->getLiterals();
  Assert(!lits.empty());
  for (const Node& l : lits)
  {
    d_litsToAssigners[l].push_back(a);
  }
}
bool AssignerDb::hasAssigners() const { return !d_db.empty(); }

const std::vector<Assigner*>& AssignerDb::getAssignersFor(const Node& lit) const
{
  std::map<Node, std::vector<Assigner*>>::const_iterator it =
      d_litsToAssigners.find(lit);
  if (it == d_litsToAssigners.end())
  {
    return d_emptyVec;
  }
  return it->second;
}

}  // namespace cvc5::internal
