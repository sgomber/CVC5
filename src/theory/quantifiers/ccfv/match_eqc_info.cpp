/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Info per equivalence class for matching in CCFV.
 */

#include "theory/quantifiers/ccfv/match_eqc_info.h"

#include "expr/node_algorithm.h"
#include "theory/quantifiers/ccfv/state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/uf/equality_engine_iterator.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

void MatchEqcInfo::initialize(TNode r,
                              const State& s,
                              eq::EqualityEngine* ee,
                              TermDb* tdb)
{
  Assert(ee->hasTerm(r));
  Assert(ee->getRepresentative(r) == r);
  NodeManager* nm = NodeManager::currentNM();
  eq::EqClassIterator eqc_i = eq::EqClassIterator(r, ee);
  while (!eqc_i.isFinished())
  {
    TNode n = (*eqc_i);
    ++eqc_i;
    if (!expr::hasFreeVar(n))
    {
      // could have a pattern that was already merged, skip it
      continue;
    }
    Node matchOp = tdb->getMatchOperator(n);
    if (matchOp.isNull())
    {
      continue;
    }
    // normalize arguments based on representatives?
    std::vector<Node> args;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      args.push_back(n.getOperator());
    }
    bool childChanged = false;
    for (TNode nc : n)
    {
      TNode ncr = s.getGroundRepresentative(nc);
      args.push_back(ncr);
      childChanged = childChanged || ncr != nc;
    }
    Node nn = childChanged ? Node(n) : nm->mkNode(n.getKind(), args);
    std::vector<Node>& ms = d_matchOps[matchOp];
    if (std::find(ms.begin(), ms.end(), nn) == ms.end())
    {
      ms.push_back(nn);
    }
  }
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
