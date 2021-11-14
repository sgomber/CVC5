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
 * State for congruence closure with free variables
 */

#include "theory/quantifiers/ccfv/state.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

State::State(Env& env) : EnvObj(env)
{
}

QuantInfo& State::getQuantInfo(TNode q)
{
  std::map<Node, QuantInfo>::iterator it = d_quantInfo.find(q);
  if(it != d_quantInfo.end())
  {
    return it->second;
  }
  d_quantInfo.emplace(q, context());
  return d_quantInfo[q];
}

const QuantInfo& State::getQuantInfo(TNode q) const
{
  std::map<Node, QuantInfo>::const_iterator it = d_quantInfo.find(q);
  Assert(it != d_quantInfo.end());
  return it->second;
}

FreeVarInfo& State::getOrMkFreeVarInfo(TNode v)
{
  std::map<Node, FreeVarInfo>::iterator it = d_fvInfo.find(v);
  if(it != d_fvInfo.end())
  {
    return it->second;
  }
  d_fvInfo.emplace(v, context());
  return d_fvInfo[v];
}

const FreeVarInfo& State::getFreeVarInfo(TNode v) const
{
  std::map<Node, FreeVarInfo>::const_iterator it = d_fvInfo.find(v);
  Assert(it != d_fvInfo.end());
  return it->second;
}

PatTermInfo& State::getOrMkPatTermInfo(TNode p)
{
  std::map<Node, PatTermInfo>::iterator it = d_pInfo.find(p);
  if(it != d_pInfo.end())
  {
    return it->second;
  }
  d_pInfo.emplace(p, context());
  return d_pInfo[p];
}

const PatTermInfo& State::getPatTermInfo(TNode p) const
{
  std::map<Node, PatTermInfo>::const_iterator it = d_pInfo.find(p);
  Assert(it != d_pInfo.end());
  return it->second;
}

EqcInfo& State::getOrMkEqcInfo(TNode r)
{
  std::map<Node, EqcInfo>::iterator it = d_eqcInfo.find(r);
  if(it != d_eqcInfo.end())
  {
    return it->second;
  }
  d_eqcInfo.emplace(r, context());
  return d_eqcInfo[r];
}


}  // namespace quantifiers
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
