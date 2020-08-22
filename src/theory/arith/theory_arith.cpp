/*********************                                                        */
/*! \file theory_arith.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andrew Reynolds, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/theory_arith.h"

#include "options/smt_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/equality_solver.h"
#include "theory/arith/infer_bounds.h"
#include "theory/arith/theory_arith_private.h"
#include "theory/ext_theory.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

TheoryArith::TheoryArith(context::Context* c,
                         context::UserContext* u,
                         OutputChannel& out,
                         Valuation valuation,
                         const LogicInfo& logicInfo,
                         ProofNodeManager* pnm)
    : Theory(THEORY_ARITH, c, u, out, valuation, logicInfo, pnm),
      d_internal(
          new TheoryArithPrivate(*this, c, u, out, valuation, logicInfo, pnm)),
      d_ppRewriteTimer("theory::arith::ppRewriteTimer"),
      d_proofRecorder(nullptr),
      d_astate(*d_internal, c, u, valuation),
      d_im(*this, d_astate),
      d_eqSolver(options::arithEqSolver() ? new EqualitySolver(d_astate, d_im)
                                          : nullptr),
      d_aim(*this, d_astate, *d_internal, d_eqSolver.get())
{
  smtStatisticsRegistry()->registerStat(&d_ppRewriteTimer);

  // indicate we are using the theory state object and inference manager
  d_theoryState = &d_astate;
  d_inferManager = &d_im;
}

TheoryArith::~TheoryArith(){
  smtStatisticsRegistry()->unregisterStat(&d_ppRewriteTimer);
  delete d_internal;
}

TheoryRewriter* TheoryArith::getTheoryRewriter()
{
  return d_internal->getTheoryRewriter();
}

bool TheoryArith::needsEqualityEngine(EeSetupInfo& esi)
{
  if (d_eqSolver != nullptr)
  {
    return d_eqSolver->needsEqualityEngine(esi);
  }
  return d_internal->needsEqualityEngine(esi);
}
void TheoryArith::finishInit()
{
  if (getLogicInfo().isTheoryEnabled(THEORY_ARITH)
      && getLogicInfo().areTranscendentalsUsed())
  {
    // witness is used to eliminate square root
    d_valuation.setUnevaluatedKind(kind::WITNESS);
    // we only need to add the operators that are not syntax sugar
    d_valuation.setUnevaluatedKind(kind::EXPONENTIAL);
    d_valuation.setUnevaluatedKind(kind::SINE);
    d_valuation.setUnevaluatedKind(kind::PI);
  }
  // finish initialize internally
  d_internal->finishInit();

  // setup the equality engine
  if (d_eqSolver != nullptr)
  {
    Assert(d_equalityEngine != nullptr);
    d_eqSolver->setEqualityEngine(d_equalityEngine);
  }
}

void TheoryArith::preRegisterTerm(TNode n) { d_internal->preRegisterTerm(n); }

TrustNode TheoryArith::expandDefinition(Node node)
{
  return d_internal->expandDefinition(node);
}

void TheoryArith::notifySharedTerm(TNode n) { d_internal->notifySharedTerm(n); }

TrustNode TheoryArith::ppRewrite(TNode atom)
{
  CodeTimer timer(d_ppRewriteTimer, /* allow_reentrant = */ true);
  return d_internal->ppRewrite(atom);
}

Theory::PPAssertStatus TheoryArith::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  return d_internal->ppAssert(in, outSubstitutions);
}

void TheoryArith::ppStaticLearn(TNode n, NodeBuilder<>& learned) {
  d_internal->ppStaticLearn(n, learned);
}

bool TheoryArith::preCheck(Effort level) { return d_internal->preCheck(level); }

void TheoryArith::postCheck(Effort level) { d_internal->postCheck(level); }

bool TheoryArith::preNotifyFact(TNode atom, bool pol, TNode fact, bool isPrereg)
{
  if (d_eqSolver != nullptr)
  {
    // assert equalities directly to equality engine
    if (!d_eqSolver->preNotifyFact(atom, pol, fact))
    {
      return false;
    }
  }
  d_internal->notifyFact(atom, pol, fact);
  return true;
}

void TheoryArith::notifyFact(TNode atom, bool pol, TNode fact, bool isInternal)
{
  Assert(d_eqSolver != nullptr);
  d_eqSolver->notifyFact(atom, pol, fact, isInternal);
  // if not in conflict from pure equality
  if (!d_astate.isInConflict())
  {
    d_internal->notifyFact(atom, pol, fact);
  }
}

bool TheoryArith::needsCheckLastEffort() {
  return d_internal->needsCheckLastEffort();
}

TrustNode TheoryArith::explain(TNode n)
{
#if 0
  return d_aim.explain(n);
#endif
  if (d_eqSolver != nullptr)
  {
    TrustNode teqExp = d_eqSolver->explainLit(n);
    if (!teqExp.isNull())
    {
      return teqExp;
    }
  }
  Node exp = d_internal->explain(n);
  return TrustNode::mkTrustPropExp(n, exp, nullptr);
}

bool TheoryArith::getCurrentSubstitution( int effort, std::vector< Node >& vars, std::vector< Node >& subs, std::map< Node, std::vector< Node > >& exp ) {
  return d_internal->getCurrentSubstitution( effort, vars, subs, exp );
}

bool TheoryArith::isExtfReduced( int effort, Node n, Node on, std::vector< Node >& exp ) {
  return d_internal->isExtfReduced( effort, n, on, exp );
}

void TheoryArith::propagate(Effort e) {
  d_internal->propagate(e);
}

bool TheoryArith::collectModelInfo(TheoryModel* m)
{
  std::set<Node> termSet;
  computeRelevantTerms(termSet);
  // overrides behavior to not assert the equality engine
  return collectModelValues(m, termSet);
}

bool TheoryArith::collectModelValues(TheoryModel* m, std::set<Node>& termSet)
{
  return d_internal->collectModelValues(m, termSet);
}

void TheoryArith::notifyRestart(){
  d_internal->notifyRestart();
}

void TheoryArith::presolve(){
  d_internal->presolve();
}

EqualityStatus TheoryArith::getEqualityStatus(TNode a, TNode b) {
  return d_internal->getEqualityStatus(a,b);
}

Node TheoryArith::getModelValue(TNode var) {
  return d_internal->getModelValue( var );
}

std::pair<bool, Node> TheoryArith::entailmentCheck(TNode lit)
{
  ArithEntailmentCheckParameters def;
  def.addLookupRowSumAlgorithms();
  ArithEntailmentCheckSideEffects ase;
  std::pair<bool, Node> res = d_internal->entailmentCheck(lit, def, ase);
  return res;
}

void TheoryArith::lemmaPrivate(TNode lem) { d_out->lemma(lem); }

void TheoryArith::propagatePrivateLit(TNode literal)
{
#if 0
  return d_aim.propagateManagedLit(literal, true);
#endif
  if (d_eqSolver != nullptr)
  {
    if (d_eqSolver->hasPropagated(literal))
    {
      // don't propagate what already was propagated
      return;
    }
    d_eqSolver->notifyPropagated(literal);
  }
  d_out->propagate(literal);
}

void TheoryArith::conflictPrivate(TNode conf) { d_out->conflict(conf); }

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
