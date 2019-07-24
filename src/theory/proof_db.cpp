/*********************                                                        */
/*! \file proof_db.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of Proof db.
 **/

#include "theory/proof_db.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

void ProofDbRule::init(const std::string& name, Node cond, Node eq)
{
  d_name = name;
  d_cond = cond;
  d_eq = eq;
}

ProofDb::ProofDb() : d_idCounter(1), d_notify(*this) {}

void ProofDb::registerRules(const std::map<Node, std::string>& rules)
{
  // TODO
  for (const std::pair<const Node, std::string>& rr : rules)
  {
    Node r = rr.first;
    AlwaysAssert(r.getKind() == IMPLIES);

    // must canonize
    Trace("proof-db") << "Add rule " << r[1] << std::endl;
    Node cr = d_canon.getCanonicalTerm(r);

    Node cond = cr[0];
    Node eq = cr[1];

    // add to discrimination tree
    Trace("proof-db-debug") << "Add (Canonical) rule " << eq << std::endl;
    d_mt.addTerm(eq);

    // remember rules
    d_ids[eq].push_back(d_idCounter);
    d_proofDbRule[d_idCounter].init(rr.second, cond, eq);
    d_idCounter++;
  }
}

bool ProofDb::existsRule(Node a, Node b, unsigned& index)
{
  if (a == b)
  {
    // reflexivity
    return true;
  }
  if (b.isConst())
  {
    // nullary symbols should not rewrite to constants
    Assert(a.getNumChildren() != 0);
    bool allConst = true;
    for (const Node& ac : a)
    {
      if (!ac.isConst())
      {
        allConst = false;
      }
    }
    if (allConst)
    {
      // evaluation
      return true;
    }
  }
  Kind ak = a.getKind();
  Kind bk = b.getKind();
  if (ak == EQUAL && a[0] == a[1])
  {
    Assert(b.isConst() && b.getConst<bool>());
    // rewriting reflexive equality to true
    return true;
  }
  if (ak == EQUAL && bk == EQUAL)
  {
    if (a[0] == b[1] && b[0] == a[1])
    {
      // symmetry of equality
      return true;
    }
  }
  Node eq = a.eqNode(b);
  // is an instance of existing rule?
  if (!d_mt.getMatches(eq, &d_notify))
  {
    return true;
  }

  return false;
}

bool ProofDb::existsRule(Node a, Node b)
{
  unsigned index = 0;
  return existsRule(a, b, index);
}

bool ProofDb::proveRule(Node a, Node b)
{
  Assert(!existsRule(a, b));
  // trusted reduction, try to prove

  return false;
}

void ProofDb::notify(Node a, Node b)
{
  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
  notify(a, b, *nodeManagerOptions.getOut());
}

void ProofDb::notify(Node a, Node b, std::ostream& out)
{
  if (existsRule(a, b))
  {
    // already exists
    return;
  }
  out << "(trusted (= " << a << " " << b << "))" << std::endl;
}

bool ProofDb::notifyMatch(Node s,
                          Node n,
                          std::vector<Node>& vars,
                          std::vector<Node>& subs)
{
  Trace("proof-db-infer") << "ProofDb::notifyMatch: " << s
                          << " is instance of existing rule:" << std::endl;
  Trace("proof-db-infer") << "  " << n << std::endl;
  Trace("proof-db-infer") << "  substitution: " << vars << " -> " << subs
                          << std::endl;
  return true;
}

}  // namespace theory
}  // namespace CVC4
