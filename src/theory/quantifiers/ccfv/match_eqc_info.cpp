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
  Assert(s.isGroundEqc(r));
  Assert(ee->hasTerm(r));
  // the ground representative is not necessarily the representive, convert here
  TNode eer = ee->getRepresentative(r);
  NodeManager* nm = NodeManager::currentNM();
  eq::EqClassIterator eqc_i = eq::EqClassIterator(eer, ee);
  while (!eqc_i.isFinished())
  {
    TNode n = (*eqc_i);
    ++eqc_i;
    // NOTE: this is not necessary?
    /*
    if (!expr::hasBoundVar(n))
    {
      // could have a pattern that was already merged, skip it
      continue;
    }
    */
    Node matchOp = tdb->getMatchOperator(n);
    if (matchOp.isNull())
    {
      continue;
    }
    // normalize arguments based on *ground* representatives from the state
    std::vector<Node> args;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      args.push_back(n.getOperator());
    }
    bool success = true;
    bool childChanged = false;
    for (TNode nc : n)
    {
      TNode ncr = s.getGroundRepresentative(nc);
      if (ncr.isNull())
      {
        success = false;
        break;
      }
      args.push_back(ncr);
      childChanged = childChanged || ncr != nc;
    }
    if (!success)
    {
      // the term had an argument that we did not find a ground representative
      // for
      continue;
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
