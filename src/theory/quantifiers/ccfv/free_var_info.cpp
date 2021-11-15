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
 * Info per free variable in CCFV.
 */

#include "theory/quantifiers/ccfv/free_var_info.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

FreeVarInfo::FreeVarInfo(context::Context* c) : d_useList(c), d_quantList(c), d_context(c) {}

void FreeVarInfo::resetRound()
{
  d_eqcProcessed.clear();
  d_qindex = 0;
  d_itql = d_qlist.begin();
}

bool FreeVarInfo::isFinished() const
{
  return d_itql==d_qlist.end();
}

void FreeVarInfo::addQuantMatch(TNode f, size_t index, TNode q)
{
  std::pair<TNode, size_t> key(f, index);
  std::map<std::pair<TNode, size_t>, NodeList>::iterator it = d_qlist.find(key);
  if (it == d_qlist.end())
  {
    it = d_qlist.emplace(key, d_context).first;
  }
  it->second.push_back(q);
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
