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

#include "theory/strings/theory_strings_utils.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

EagerSolver::EagerSolver(SolverState& state, options::StringsEagerSolverMode m) : d_state(state), d_mode(m) {}

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
  if (d_mode==options::StringsEagerSolverMode::NONE)
  {
    return;
  }
  
  if (t.isConst())
  {
    if (t.getType().isStringLike())
    {
      EqcInfo* ei = d_state.getOrMakeEqcInfo(t);
      ei->initializeConstant(t);
    }
  }
  else if (k == STRING_CONCAT)
  {
    addEndpointsToEqcInfo(t, t, t, d_null);
  }
}

void EagerSolver::eqNotifyMerge(TNode t1, TNode t2)
{
  EqcInfo* e2 = d_state.getOrMakeEqcInfo(t2, false);
  if (e2 == nullptr)
  {
    return;
  }
  Assert(t1.getType().isStringLike());
  EqcInfo* e1 = d_state.getOrMakeEqcInfo(t1);
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

  // if we aren't doing eager techniques, return now
  if (d_mode==options::StringsEagerSolverMode::NONE)
  {
    return;
  }
  
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

void EagerSolver::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  if (t1.getType().isStringLike())
  {
    // store disequalities between strings, may need to check if their lengths
    // are equal/disequal
    d_state.addDisequality(t1, t2);
  }
}

void EagerSolver::addEndpointsToEqcInfo(Node r, Node t, Node concat, Node exp)
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
      addEndpointsToEqcInfo(eqc, atom[0], atom[1], atom);
    }
  }
}

Node EagerSolver::getBestContent(Node f, std::vector<Node>& exp)
{
  Kind fk = f.getKind();
  if (!d_state.getEqualityEngine()->isFunctionKind(fk))
  {
    return f;
  }
  // strings does not have parametrized kinds for congruence kinds
  Assert (f.getMetaKind() != metakind::PARAMETERIZED);
  std::vector<Node> children;
  for (const Node& fc : f)
  {
    children.push_back(getBestContentArg(fc,exp));
  }
  if (exp.empty())
  {
    return f;
  }
  Node ret = NodeManager::currentNM()->mkNode(fk, children);
  ret = Rewriter::rewrite(ret);
  return ret;
}

Node EagerSolver::getBestContentArg(Node t, std::vector<Node>& exp)
{
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  Node r = ee->getRepresentative(t);
  EqcInfo* e = d_state.getOrMakeEqcInfo(r, false);
  if (e==nullptr)
  {
    return t;
  }
  // 
  //Node rt = e->d_prefixC.d_t.get();
  
  
  // TODO
  return t;
}

Node EagerSolver::checkConflict(Node t, Node c)
{
  return Node::null();
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
