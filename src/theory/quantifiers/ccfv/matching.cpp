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
 * Congruence closure with free variables
 */

#include "theory/quantifiers/ccfv/matching.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/uf/equality_engine.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

Matching::Matching(Env& env,
                       State& state,
                       QuantifiersState& qs)
    : EnvObj(env),
      d_state(state),
      d_qstate(qs)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

bool Matching::processMatcher(QuantInfo& qi, TNode matcher)
{
  PatTermInfo& pi = d_state.getPatTermInfo(matcher);
  if (!pi.isActive())
  {
    return false;
  }
  TypeNode tn = matcher.getType();
  // get constraints to determine initial equivalence classes
  const std::map<TNode, std::vector<Node>>& cs = qi.getConstraints();
  TNode eq;
  std::vector<TNode> deq;
  std::map<TNode, std::vector<Node>>::const_iterator itc = cs.find(matcher);
  if (itc != cs.end())
  {
    bool setInactive = false;
    for (const Node& cc : itc->second)
    {
      if (cc.isNull())
      {
        // constraint says that the term must be equal to anything
        continue;
      }
      TNode dval;
      if (QuantInfo::isDeqConstraint(cc, matcher, dval))
      {
        Assert(!tn.isBoolean());
        Assert(!dval.isNull());
        dval = d_state.getGroundRepresentative(dval);
        if (!dval.isNull())
        {
          if (eq.isNull())
          {
            deq.push_back(dval);
          }
          else if (eq == dval)
          {
            // term must be equal and disequal to the same thing
            setInactive = true;
          }
        }
        else
        {
          // the pattern needs to be disequal to a term that does not exist
          setInactive = true;
        }
      }
      else
      {
        TNode eval = d_state.getGroundRepresentative(cc);
        if (!eval.isNull())
        {
          if (eq.isNull())
          {
            // also check if disequality constraints contradict
            if (std::find(deq.begin(), deq.end(), eq) != deq.end())
            {
              // term must be equal and disequal to the same thing
              setInactive = true;
            }
            else
            {
              eq = eval;
            }
            deq.clear();
          }
          else if (eval != eq)
          {
            // Matcher needs to be equal to two different things that are not
            // equal. This should happen very infrequently, e.g.
            // forall x. (f(x) = a ^ f(x) = b) => P(x) where a is not currently
            // equal to b.
            setInactive = true;
          }
        }
        else
        {
          // the pattern needs to be equal to a term that does not exist
          setInactive = true;
        }
      }
      if (setInactive)
      {
        d_state.setQuantInactive(qi);
        return false;
      }
    }
  }
  // if we have an equality constraint, we limit to matching in that equivalence
  // class
  if (!eq.isNull())
  {
    Assert(d_state.isGroundEqc(eq));
    pi.addWatchEqc(eq);
  }
  else
  {
    // otherwise, we must consider all equivalence clases
    if (tn.isBoolean())
    {
      Assert(deq.empty());
      pi.addWatchEqc(d_true);
      pi.addWatchEqc(d_false);
    }
    else
    {
      // if not Boolean, we can filter by deq
      const std::unordered_set<TNode>& eqcs = d_state.getGroundEqcFor(tn);
      for (TNode eqc : eqcs)
      {
        if (std::find(deq.begin(), deq.end(), eqc) == deq.end())
        {
          pi.addWatchEqc(eqc);
        }
      }
    }
  }
  // now run matching
  runMatching(&pi);
  return true;
}

void Matching::runMatching(PatTermInfo* pi)
{
  Assert(pi != nullptr);
  TNode op = pi->d_matchOp;
  if (op.isNull())
  {
    // If not a matchable operator. This is also the base case of
    // BOUND_VARIABLE.
    return;
  }
  TNode weqc = pi->getNextWatchEqc();
  if (weqc.isNull())
  {
    // no new equivalence classes to process
    return;
  }
  std::vector<TNode> pargs;
  std::vector<PatTermInfo*> piargs;
  std::vector<size_t> matchIndices;
  std::vector<size_t> nmatchIndices;
  std::unordered_map<TNode, std::vector<Node>>::iterator itm;
  while (!weqc.isNull())
  {
    Assert(d_state.isGroundEqc(weqc));
    MatchEqcInfo& meqc = d_state.getMatchEqcInfo(weqc);

    // get the terms to match in this equivalence class
    itm = meqc.d_matchOps.find(op);
    if (itm == meqc.d_matchOps.end())
    {
      // no matchable terms in this equivalence class
    }
    else
    {
      // set up the matching information for pi->d_pattern
      if (pargs.empty())
      {
        // get the status of the arguments of pi
        Assert(pi->d_pattern.getNumChildren() > 0);
        for (size_t i = 0, nchild = pi->d_pattern.getNumChildren(); i < nchild;
             i++)
        {
          TNode pic = pi->d_pattern[i];
          // Note we use get ground representative here. We do not use getValue,
          // which should never be sink.
          TNode gpic = d_state.getGroundRepresentative(pic);
          pargs.push_back(gpic);
          if (!gpic.isNull())
          {
            matchIndices.push_back(i);
            piargs.push_back(nullptr);
          }
          else
          {
            nmatchIndices.push_back(i);
            piargs.push_back(&d_state.getPatTermInfo(pic));
          }
        }
        // we should not have ground representatives for each child of the
        // pattern, otherwise we should be fully assigned
        Assert(!nmatchIndices.empty());
      }
      // none in this equivalence class
      // for each term with the same match operator
      bool isMaybeEq = false;
      for (const Node& m : itm->second)
      {
        Assert(m.getNumChildren() == pargs.size());
        bool matchSuccess = true;
        for (size_t i : matchIndices)
        {
          Assert(d_state.isGroundEqc(m[i]));
          if (pargs[i] != m[i])
          {
            matchSuccess = false;
            break;
          }
        }
        // if successful, we will match the children of this pattern to the
        // ground equivalence class
        if (matchSuccess)
        {
          for (size_t i : nmatchIndices)
          {
            piargs[i]->addWatchEqc(m[i]);
            // recurse to do matching on the argument
            runMatching(piargs[i]);
            // if it is not possible that we are equal, we stop matching this
            // term
            if (!piargs[i]->isMaybeEqc(m[i]))
            {
              matchSuccess = false;
              break;
            }
          }
          isMaybeEq = isMaybeEq || matchSuccess;
        }
      }
      // if its possible that we are equal by matching, record this here
      if (isMaybeEq)
      {
        pi->addMaybeEqc(weqc);
      }
    }
    // increment weqc to the next equivalence class
    weqc = pi->getNextWatchEqc();
  }
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
