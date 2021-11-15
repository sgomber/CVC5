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

#include "theory/quantifeirs/term_database.h"
#include "theory/uf/equality_engine_iterator.h"


namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

void MatchEqcInfo::initialize(TNode r, eq::EqualityEngine * ee, TermDb* tdb)
{
  Assert (ee->hasTerm(r));
  Assert (ee->getRepresentative(r)==r);
  eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
  while( !eqc_i.isFinished() )
  {
    TNode n = (*eqc_i);
    ++eqc_i;
    Node matchOp = tdb->getMatchOperator(n);
    if (matchOp.isNull())
    {
      continue;
    }
    d_matchOps[matchOp].push_back(n);
  }
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
