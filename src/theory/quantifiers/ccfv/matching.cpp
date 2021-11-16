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
#include "theory/quantifiers/term_database.h"
#include "theory/uf/equality_engine.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

Matching::Matching(Env& env, State& state, QuantifiersState& qs, TermDb* tdb)
    : EnvObj(env), d_state(state), d_qstate(qs), d_tdb(tdb)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

void Matching::initializeLevel(size_t level) { d_mpmap[level].clear(); }

bool Matching::processMatcher(size_t level, QuantInfo& qi, TNode matcher)
{
  // the matcher should be active, or otherwise the quantified formula should
  // have been marked inactive.
  Assert(d_state.getPatTermInfo(matcher).isActive());
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
        Assert(!matcher.getType().isBoolean());
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
  // get the match pattern info
  std::map<TNode, MatchPatInfo>& mmp = getMatchPatInfo(level);
  MatchPatInfo* mpi = &mmp[matcher];
  // if we have an equality constraint, we limit to matching in that equivalence
  // class
  if (!eq.isNull())
  {
    Assert(d_state.isGroundEqc(eq));
    mpi->addWatchEqc(eq);
  }
  else
  {
    TypeNode tn = matcher.getType();
    // otherwise, we must consider all equivalence clases
    if (tn.isBoolean())
    {
      Assert(deq.empty());
      mpi->addWatchEqc(d_true);
      mpi->addWatchEqc(d_false);
    }
    else
    {
      // if not Boolean, we can filter by deq
      const std::unordered_set<TNode>& eqcs = d_state.getGroundEqcFor(tn);
      for (TNode eqc : eqcs)
      {
        if (std::find(deq.begin(), deq.end(), eqc) == deq.end())
        {
          mpi->addWatchEqc(eqc);
        }
      }
    }
  }
  // now run matching
  runMatching(mmp, matcher, mpi);
  return true;
}

void Matching::runMatching(std::map<TNode, MatchPatInfo>& mmp,
                           TNode p,
                           MatchPatInfo* mpi)
{
  Assert(pi != nullptr);
  Assert(mpi != nullptr);
  TNode op = d_tdb->getMatchOperator(p);
  if (op.isNull())
  {
    // If not a matchable operator. This is also the base case of
    // BOUND_VARIABLE.
    return;
  }
  TNode weqc = mpi->getNextWatchEqc();
  if (weqc.isNull())
  {
    // no new equivalence classes to process
    return;
  }
  // the ground representatives of the pattern, if they exist
  std::vector<TNode> pargs;
  // pattern term information for
  std::vector<MatchPatInfo*> mpiargs;
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
      // set up the matching information for p
      if (pargs.empty())
      {
        // get the status of the arguments of pi
        Assert(p.getNumChildren() > 0);
        for (size_t i = 0, nchild = p.getNumChildren(); i < nchild; i++)
        {
          TNode pic = p[i];
          // Note we use get ground representative here. We do not use getValue,
          // which should never be sink.
          TNode gpic = d_state.getGroundRepresentative(pic);
          pargs.push_back(gpic);
          if (!gpic.isNull())
          {
            matchIndices.push_back(i);
            mpiargs.push_back(nullptr);
          }
          else
          {
            nmatchIndices.push_back(i);
            mpiargs.push_back(&mmp[pic]);
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
            mpiargs[i]->addWatchEqc(m[i]);
            if (p[i].getKind() == BOUND_VARIABLE)
            {
              // don't need to run matching on variables
              continue;
            }
            // recurse to do matching on the argument
            runMatching(mmp, p[i], mpiargs[i]);
            // if it is not possible that we are equal, we stop matching this
            // term
            if (!mpiargs[i]->isMaybeEqc(m[i]))
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
        mpi->addMaybeEqc(weqc);
      }
    }
    // increment weqc to the next equivalence class
    weqc = mpi->getNextWatchEqc();
  }
}

std::map<TNode, MatchPatInfo>& Matching::getMatchPatInfo(size_t level)
{
  return d_mpmap[level];
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
