/*********************                                                        */
/*! \file theory_proxy.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "prop/theory_proxy.h"

#include "context/context.h"
#include "decision/decision_engine.h"
#include "options/decision_options.h"
#include "options/prop_options.h"
#include "options/smt_options.h"
#include "proof/cnf_proof.h"
#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "prop/sat_relevancy.h"
#include "smt/smt_statistics_registry.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace prop {

TheoryProxy::TheoryProxy(PropEngine* propEngine,
                         TheoryEngine* theoryEngine,
                         DecisionEngine* decisionEngine,
                         context::Context* context,
                         context::UserContext* userContext,
                         ProofNodeManager* pnm)
    : d_propEngine(propEngine),
      d_cnfStream(nullptr),
      d_decisionEngine(decisionEngine),
      d_context(context),
      d_userContext(userContext),
      d_theoryEngine(theoryEngine),
      d_queue(context),
      d_satRlv(nullptr),
      d_tpp(*theoryEngine, userContext, pnm)
{
}

TheoryProxy::~TheoryProxy() {
  /* nothing to do for now */
}

void TheoryProxy::finishInit(CDCLTSatSolverInterface* satSolver,
                             CnfStream* cnfStream)
{
  d_cnfStream = cnfStream;

  if (options::satTheoryRelevancy() != options::SatRelevancyMode::NONE)
  {
    d_satRlv.reset(new SatRelevancy(satSolver,
                                    d_theoryEngine,
                                    d_context,
                                    d_userContext,
                                    cnfStream,
                                    options::satTheoryRelevancy()));
    d_skdm.reset(new SkolemDefManager(d_context,
                                      d_userContext,
                                      d_tpp.getRemoveTermFormulas()));
  }
}

void TheoryProxy::notifyPreprocessedAssertions(
    const std::vector<Node>& assertions)
{
  d_theoryEngine->notifyPreprocessedAssertions(assertions);
}

void TheoryProxy::presolve()
{
  d_theoryEngine->presolve();
  if (d_satRlv != nullptr)
  {
    d_satRlv->presolve(d_queue);
  }
}

void TheoryProxy::notifyAssertion(TNode a, TNode skolem)
{
  if (d_satRlv != nullptr)
  {
    if (skolem.isNull())
    {
      // an input assertion
      // NOTE: we don't currently distinguish input from lemmas since unit
      // input formulas trigger assertions before input, thus, adding a formula
      // may trigger assertions to add to d_queue already here.
      d_satRlv->notifyLemma(a, d_queue);
    }
    else
    {
      // a skolem definition from input
      d_skdm->notifySkolemDefinition(skolem, a);
    }
  }
}

void TheoryProxy::notifyLemma(TNode lem, TNode skolem)
{
  // notify the skolem definition manager if it exists
  if (d_satRlv != nullptr)
  {
    if (skolem.isNull())
    {
      // a new theory lemma
      d_satRlv->notifyLemma(lem, d_queue);
    }
    else
    {
      // a skolem definition from a lemma
      d_skdm->notifySkolemDefinition(skolem, lem);
    }
  }
}

void TheoryProxy::variableNotify(SatVariable var) {
  Node n = d_cnfStream->getNode(SatLiteral(var));
  if (d_satRlv != nullptr)
  {
    d_satRlv->notifyVarNotify(n);
  }
  else
  {
    d_theoryEngine->preRegister(n);
  }
}

void TheoryProxy::theoryCheck(theory::Theory::Effort effort) {
  if (d_satRlv != nullptr)
  {
    d_satRlv->check(effort, d_queue);
  }
  while (!d_queue.empty()) {
    TNode assertion = d_queue.front();
    d_queue.pop();
    // now, assert to theory engine
    d_theoryEngine->assertFact(assertion);
    if (d_satRlv != nullptr)
    {
      Assert (d_skdm != nullptr);
      Trace("sat-rlv-assert")
          << "Assert to theory engine: " << assertion << std::endl;
      // assertion processed makes all skolems in assertion active,
      // which triggers their definitions to becoming relevant
      std::vector<TNode> activatedSkolems;
      d_skdm->notifyAsserted(assertion, activatedSkolems);
      for (const Node& k : activatedSkolems)
      {
        Node def = d_skdm->getSkolemDefinitionFor(k);
        d_satRlv->notifyActivatedSkolemDef(def, d_queue);
      }
    }
  }
  // check with the theory engine
  d_theoryEngine->check(effort);
}

void TheoryProxy::theoryPropagate(std::vector<SatLiteral>& output) {
  // Get the propagated literals
  std::vector<TNode> outputNodes;
  d_theoryEngine->getPropagatedLiterals(outputNodes);
  for (unsigned i = 0, i_end = outputNodes.size(); i < i_end; ++ i) {
    Debug("prop-explain") << "theoryPropagate() => " << outputNodes[i] << std::endl;
    /*
    // TEMPORARY
    if (d_satRlv != nullptr)
    {
      d_satRlv->notifyPropagate(outputNodes[i]);
    }
    */
    output.push_back(d_cnfStream->getLiteral(outputNodes[i]));
  }
}

void TheoryProxy::explainPropagation(SatLiteral l, SatClause& explanation) {
  TNode lNode = d_cnfStream->getNode(l);
  Debug("prop-explain") << "explainPropagation(" << lNode << ")" << std::endl;

  theory::TrustNode tte = d_theoryEngine->getExplanation(lNode);
  Node theoryExplanation = tte.getNode();
  if (CVC4::options::produceProofs())
  {
    d_propEngine->getProofCnfStream()->convertPropagation(tte);
  }
  else if (options::unsatCores())
  {
    ProofManager::getCnfProof()->pushCurrentAssertion(theoryExplanation);
  }
  Debug("prop-explain") << "explainPropagation() => " << theoryExplanation
                        << std::endl;
  explanation.push_back(l);
  if (theoryExplanation.getKind() == kind::AND)
  {
    for (const Node& n : theoryExplanation)
    {
      explanation.push_back(~d_cnfStream->getLiteral(n));
    }
  }
  else
  {
    explanation.push_back(~d_cnfStream->getLiteral(theoryExplanation));
  }
  if (Trace.isOn("sat-proof"))
  {
    std::stringstream ss;
    ss << "TheoryProxy::explainPropagation: clause for lit is ";
    for (unsigned i = 0, size = explanation.size(); i < size; ++i)
    {
      ss << explanation[i] << " [" << d_cnfStream->getNode(explanation[i])
         << "] ";
    }
    Trace("sat-proof") << ss.str() << "\n";
  }
}

void TheoryProxy::enqueueTheoryLiteral(const SatLiteral& l) {
  if (d_satRlv != nullptr)
  {
    // use the sat relevancy to enqueue literals that are relevant
    d_satRlv->notifyAsserted(l, d_queue);
    return;
  }
  Node literalNode = d_cnfStream->getNode(l);
  Debug("prop") << "enqueueing theory literal " << l << " " << literalNode << std::endl;
  Assert(!literalNode.isNull());
  d_queue.push(literalNode);
}

SatLiteral TheoryProxy::getNextTheoryDecisionRequest() {
  TNode n = d_theoryEngine->getNextDecisionRequest();
  // it becomes relevant in this context
  if (!n.isNull())
  {
    SatLiteral lit = d_cnfStream->getLiteral(n);
    if (d_satRlv != nullptr)
    {
      // also notify the SAT relevancy module, which will make this request
      // relevant
      d_satRlv->notifyDecisionRequest(n, d_queue);
    }
    return lit;
  }
  return undefSatLiteral;
}

SatLiteral TheoryProxy::getNextDecisionEngineRequest(bool &stopSearch) {
  Assert(d_decisionEngine != NULL);
  Assert(stopSearch != true);
  SatLiteral ret = d_decisionEngine->getNext(stopSearch);
  if(stopSearch) {
    Trace("decision") << "  ***  Decision Engine stopped search *** " << std::endl;
  }
  return options::decisionStopOnly() ? undefSatLiteral : ret;
}

bool TheoryProxy::theoryNeedCheck() const {
  return d_theoryEngine->needCheck();
}

TNode TheoryProxy::getNode(SatLiteral lit) {
  return d_cnfStream->getNode(lit);
}

void TheoryProxy::notifyRestart() {
  d_propEngine->spendResource(ResourceManager::Resource::RestartStep);
  d_theoryEngine->notifyRestart();
}

void TheoryProxy::spendResource(ResourceManager::Resource r)
{
  d_theoryEngine->spendResource(r);
}

bool TheoryProxy::isDecisionRelevant(SatVariable var) { return true; }

bool TheoryProxy::isDecisionEngineDone() {
  return d_decisionEngine->isDone();
}

SatValue TheoryProxy::getDecisionPolarity(SatVariable var) {
  return SAT_VALUE_UNKNOWN;
}

CnfStream* TheoryProxy::getCnfStream() { return d_cnfStream; }

theory::TrustNode TheoryProxy::preprocessLemma(
    theory::TrustNode trn,
    std::vector<theory::TrustNode>& newLemmas,
    std::vector<Node>& newSkolems)
{
  return d_tpp.preprocessLemma(trn, newLemmas, newSkolems);
}

theory::TrustNode TheoryProxy::preprocess(
    TNode node,
    std::vector<theory::TrustNode>& newLemmas,
    std::vector<Node>& newSkolems)
{
  return d_tpp.preprocess(node, newLemmas, newSkolems);
}

theory::TrustNode TheoryProxy::removeItes(
    TNode node,
    std::vector<theory::TrustNode>& newLemmas,
    std::vector<Node>& newSkolems)
{
  RemoveTermFormulas& rtf = d_tpp.getRemoveTermFormulas();
  return rtf.run(node, newLemmas, newSkolems, true);
}

void TheoryProxy::getSkolems(TNode node,
                             std::vector<theory::TrustNode>& skAsserts,
                             std::vector<Node>& sks)
{
  RemoveTermFormulas& rtf = d_tpp.getRemoveTermFormulas();
  std::unordered_set<Node, NodeHashFunction> skolems;
  rtf.getSkolems(node, skolems);
  for (const Node& k : skolems)
  {
    sks.push_back(k);
    skAsserts.push_back(rtf.getLemmaForSkolem(k));
  }
}

void TheoryProxy::preRegister(Node n)
{
  if (d_satRlv != nullptr)
  {
    // do nothing?
    d_satRlv->notifyPrereg(n);
  }
  else
  {
    d_theoryEngine->preRegister(n);
  }
}

}/* CVC4::prop namespace */
}/* CVC4 namespace */
