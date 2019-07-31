/*********************                                                        */
/*! \file proof_db_pf.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof data structure Proof db.
 **/

#include "theory/proof_db_pf.h"

#include "theory/proof_db_sc.h"

#include "expr/node_algorithm.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

void ProofDbRule::init(const std::string& name,
                       const std::vector<Node>& cond,
                       Node eq)
{
  d_name = name;
  d_cond.clear();
  d_cond.insert(d_cond.end(), cond.begin(), cond.end());
  d_eq = eq;

  std::unordered_set<Node, NodeHashFunction> fvs;
  expr::getFreeVariables(eq, fvs);

  d_numFv = fvs.size();

  std::unordered_set<Node, NodeHashFunction> fvsCond;
  for (const Node& c : d_cond)
  {
    expr::getFreeVariables(c, fvsCond);
  }
  std::stringstream rparens;
  Trace("proof-db-to-lfsc") << "(declare " << d_name << std::endl;
  unsigned vcounter = 0;
  for (const Node& v : fvs)
  {
    d_fvs.push_back(v);
    if (fvsCond.find(v) == fvsCond.end())
    {
      d_noOccVars[v] = true;
    }
    Trace("proof-db-to-lfsc")
        << "  (! " << v << " " << v.getType() << std::endl;
  }
  unsigned scounter = 1;
  std::vector<Node> pureconds;
  for (const Node& c : cond)
  {
    // "purify" the side conditions
    std::vector<Node> scs;
    Node cpure = ProofDbScEval::purifySideConditions(c, scs);
    pureconds.push_back(cpure);
    for (const Node& sc : scs)
    {
      Trace("proof-db-to-lfsc")
          << "  (! " << sc[1] << " " << sc[1].getType() << std::endl;
      rparens << ")";
      Trace("proof-db-to-lfsc") << "  (! u" << scounter << " (^ " << sc[0]
                                << " " << sc[1] << ")" << std::endl;
      rparens << ")";
      scounter++;
      d_numFv++;
    }
  }
  unsigned counter = 1;
  for (const Node& c : pureconds)
  {
    Trace("proof-db-to-lfsc")
        << "  (! h" << counter << " (holds " << c << ")" << std::endl;
    rparens << ")";
    counter++;
  }
  Trace("proof-db-to-lfsc")
      << "    (holds " << eq << ")" << rparens.str() << std::endl;
  Trace("proof-db-to-lfsc") << std::endl;
}

}  // namespace theory
}  // namespace CVC4
