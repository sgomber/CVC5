/*********************                                                        */
/*! \file eager_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The eager solver
 **/

#include "theory/strings/eager_solver.h"

#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

EagerSolver::EagerSolver(context::Context* c,
                         SolverState& state,
                         options::StringsEagerSolverMode m)
    : d_state(state), d_mode(m), d_mcTerms(c)
{
}

EagerSolver::~EagerSolver() {}

void EagerSolver::eqNotifyNewClass(TNode t)
{
  Kind k = t.getKind();
  if (k == STRING_LENGTH || k == STRING_TO_CODE)
  {
    eq::EqualityEngine* ee = d_state.getEqualityEngine();
    Node r = ee->getRepresentative(t[0]);
    EqcInfo* ei = d_state.getOrMakeEqcInfo(r);
    if (k == STRING_LENGTH)
    {
      ei->d_lengthTerm = t[0];
    }
    else
    {
      ei->d_codeTerm = t[0];
    }
    return;
  }
  // if we aren't doing eager techniques, return now
  if (d_mode == options::StringsEagerSolverMode::NONE)
  {
    return;
  }
  // constant strings always initialize the equivalence class info
  if (t.isConst())
  {
    if (t.getType().isStringLike())
    {
      EqcInfo* ei = d_state.getOrMakeEqcInfo(t);
      ei->initializeConstant(t);
    }
    return;
  }

  std::vector<Node> uexp;
  if (d_mode == options::StringsEagerSolverMode::FULL)
  {
    if (isFunctionKind(k))
    {
      // add the best known content of t to the equivalence class info of t
      if (addBestContent(t, t))
      {
        // added to equivalence class in the above call
        return;
      }
    }
  }

  if (k == STRING_CONCAT)
  {
    // infer prefix/suffix information
    addEndpointsToEqcInfo(t, t, t, uexp);
  }
}

void EagerSolver::eqNotifyMerge(TNode t1, TNode t2)
{
  if (d_useList.empty())
  {
    return;
  }
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  // go back and recompute the best content for the useList terms with t2
  // as an argument, since they have an argument that has updated.
  for (TNode u : d_useList)
  {
    // u should contain t1 as an argument
    Assert(isFunctionKind(u.getKind()));
    TNode r = ee->getRepresentative(u);
    addBestContent(u, r);
  }
  d_useList.clear();
}

void EagerSolver::eqNotifyPreMerge(TNode t1, TNode t2)
{
  EqcInfo* e2 = d_state.getOrMakeEqcInfo(t2, false);
  EqcInfo* e1 = nullptr;
  if (e2 != nullptr)
  {
    // must carry basic information into
    e1 = d_state.getOrMakeEqcInfo(t1);
    Assert(t1.getType().isStringLike());
    // add information from e2 to e1
    if (!e2->d_lengthTerm.get().isNull())
    {
      e1->d_lengthTerm.set(e2->d_lengthTerm);
    }
    if (!e2->d_codeTerm.get().isNull())
    {
      e1->d_codeTerm.set(e2->d_codeTerm);
    }
    if (e2->d_cardinalityLemK.get() > e1->d_cardinalityLemK.get())
    {
      e1->d_cardinalityLemK.set(e2->d_cardinalityLemK);
    }
    if (!e2->d_normalizedLength.get().isNull())
    {
      e1->d_normalizedLength.set(e2->d_normalizedLength);
    }
  }
  else
  {
    e1 = d_state.getOrMakeEqcInfo(t1, false);
  }
  // if we aren't doing eager techniques, return now
  if (d_mode == options::StringsEagerSolverMode::NONE)
  {
    return;
  }
  else if (d_mode == options::StringsEagerSolverMode::FULL)
  {
    // if we are merging into a constant
    TNode c1 = e1 != nullptr ? e1->isConst() : TNode::null();
    if (!c1.isNull())
    {
      // constant merges should already be in conflict
      Assert(e2 == nullptr || e2->isConst().isNull());
      // check whether there are conflicts
      d_state.setPendingPrefixConflictWhen(processConstantMerges(t2, c1));
      // store the use list for t2, we will notify the parents that they have
      // an argument that is now constant.
      eq::EqualityEngine* ee = d_state.getEqualityEngine();
      ee->getUseListTerms(t2, d_useList);
    }
  }

  if (e2 != nullptr)
  {
    Assert(e1 != nullptr);
    // eager prefix conflicts
    if (!e2->d_prefixC.isNull())
    {
      d_state.setPendingPrefixConflictWhen(
          e1->addEndpointConst(e2->d_prefixC, false));
    }
    if (!e2->d_suffixC.isNull())
    {
      d_state.setPendingPrefixConflictWhen(
          e1->addEndpointConst(e2->d_suffixC, true));
    }
  }
}

void EagerSolver::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  if (t1.getType().isStringLike())
  {
    // store disequalities between strings, may need to check if their lengths
    // are equal/disequal
    d_state.addDisequality(t1, t2);
  }
}

void EagerSolver::addEndpointsToEqcInfo(TNode r,
                                        TNode t,
                                        TNode concat,
                                        const std::vector<Node>& exp)
{
  Assert(concat.getKind() == STRING_CONCAT
         || concat.getKind() == REGEXP_CONCAT);
  EqcInfo* ei = nullptr;
  // check each side of the concat term
  for (unsigned i = 0; i < 2; i++)
  {
    unsigned index = i == 0 ? 0 : concat.getNumChildren() - 1;
    Node c = utils::getConstantComponent(concat[index]);
    if (!c.isNull())
    {
      if (ei == nullptr)
      {
        ei = d_state.getOrMakeEqcInfo(r);
      }
      Trace("strings-eager-pconf-debug")
          << "New term: " << concat << " for " << t << " with prefix " << c
          << " (" << (i == 1) << ")" << std::endl;
      d_state.setPendingPrefixConflictWhen(
          ei->addEndpointConst(t, c, exp, i == 1));
    }
  }
}

void EagerSolver::notifyFact(TNode atom,
                             bool polarity,
                             TNode fact,
                             bool isInternal)
{
  if (atom.getKind() == STRING_IN_REGEXP)
  {
    if (polarity && atom[1].getKind() == REGEXP_CONCAT)
    {
      eq::EqualityEngine* ee = d_state.getEqualityEngine();
      Node eqc = ee->getRepresentative(atom[0]);
      addEndpointsToEqcInfo(eqc, atom[0], atom[1], {atom});
    }
  }
}

bool EagerSolver::addBestContent(TNode f, TNode r)
{
  Assert(isFunctionKind(f.getKind()));
  std::vector<Node> exp;
  Node fc = getBestContent(f, exp);
  if (fc == f)
  {
    // did not change, nothing to do
    return false;
  }
  // we inferred equality to a constant
  if (fc.isConst())
  {
    // TODO: infer equality
  }
  else if (fc.getKind() == STRING_CONCAT)
  {
    addEndpointsToEqcInfo(r, f, fc, exp);
  }
  return true;
}

Node EagerSolver::getBestContent(TNode f, std::vector<Node>& exp)
{
  Assert(isFunctionKind(f.getKind()));
  // strings does not have parametrized kinds for congruence kinds
  Assert(f.getMetaKind() != metakind::PARAMETERIZED);
  std::vector<Node> children;
  for (TNode fc : f)
  {
    children.push_back(getBestContentArg(fc, exp));
  }
  if (exp.empty())
  {
    return f;
  }
  Node ret = NodeManager::currentNM()->mkNode(f.getKind(), children);
  ret = Rewriter::rewrite(ret);
  return ret;
}

Node EagerSolver::getBestContentArg(TNode t, std::vector<Node>& exp)
{
  if (t.isConst())
  {
    return t;
  }
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  Node r = ee->getRepresentative(t);
  EqcInfo* e = d_state.getOrMakeEqcInfo(r, false);
  if (e == nullptr)
  {
    return t;
  }
  // if its a constant, return it
  TNode tconst = e->isConst();
  if (!tconst.isNull())
  {
    Assert(t != tconst);
    exp.push_back(t.eqNode(tconst));
    return tconst;
  }
  return t;
}

/*
Node EagerSolver::getPrefixRec(Node t, std::vector<Node>& exp, bool isSuf)
{
  if (t.isConst())
  {
    return t;
  }
  else if (t.getKind()==STRING_CONCAT)
  {
    size_t index = i == 0 ? 0 : t.getNumChildren() - 1;
    return getPrefixRec(t[index], exp, isSuf);
  }
  return Node::null();
}
*/

Node EagerSolver::processConstantMerges(Node r, Node c)
{
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  Assert(ee->getRepresentative(r) == r);
  // iterate over the equivalence class and check if we infer new constant
  // terms, or otherwise infer constant
  eq::EqClassIterator eqci = eq::EqClassIterator(r, ee);
  while (!eqci.isFinished())
  {
    TNode t = *eqci;
    // skip kinds we are not doing congruence over
    if (!isFunctionKind(t.getKind()))
    {
      continue;
    }
    // TODO: could just check t == c here?
    // process
    std::vector<Node> exp;
    Node tc = getBestContent(t, exp);
    // check for an equality conflict with the constant
    if (tc == c)
    {
      // term evaluates to the constant
      // TODO: could cache that it is "evaluated" / can ignore
      continue;
    }
    Node eq = Rewriter::rewrite(tc.eqNode(c));
    if (eq.isConst() && !eq.getConst<bool>())
    {
      // conflict
      std::vector<Node> confExp;
      confExp.insert(confExp.end(), exp.begin(), exp.end());
      confExp.push_back(t.eqNode(c));
      // exp ^ t = prev.t
      Node ret = NodeManager::currentNM()->mkAnd(confExp);
      Trace("strings-eager-pconf")
          << "String: eager prefix conflict (via equality rewrite): " << ret
          << std::endl;
      return ret;
    }

    ++eqci;
  }

  return Node::null();
}

bool EagerSolver::isFunctionKind(Kind k) const
{
  return d_state.getEqualityEngine()->isFunctionKind(k);
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
