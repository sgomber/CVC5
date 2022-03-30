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
 * Oracle engine
 */

#include "theory/quantifiers/oracle_engine.h"

#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_tuple_enumerator.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/** Attribute true for input variables */
struct OracleInputVarAttributeId
{
};
typedef expr::Attribute<OracleInputVarAttributeId, bool>
    OracleInputVarAttribute;
/** Attribute true for output variables */
struct OracleOutputVarAttributeId
{
};
typedef expr::Attribute<OracleOutputVarAttributeId, bool>
    OracleOutputVarAttribute;

OracleEngine::OracleEngine(Env& env,
                           QuantifiersState& qs,
                           QuantifiersInferenceManager& qim,
                           QuantifiersRegistry& qr,
                           TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_oracleFuns(userContext()),
      d_ochecker(tr.getOracleChecker())
{
  Assert(d_ochecker != nullptr);
}

void OracleEngine::presolve() {}

// do this to play nicely
// bool InstantiationEngine::needsCheck( Theory::Effort e ){
//   return d_qstate.getInstWhenNeedsCheck(e);
// }

bool OracleEngine::needsCheck(Theory::Effort e)
{
  return e == Theory::Effort::EFFORT_LAST_CALL;
}

// the model is built at this effort level
OracleEngine::QEffort OracleEngine::needsModel(Theory::Effort e)
{
  return QEFFORT_MODEL;
}

void OracleEngine::reset_round(Theory::Effort e) {}

void OracleEngine::registerQuantifier(Node q) {}

void OracleEngine::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_MODEL)
  {
    return;
  }

  double clSet = 0;
  d_checkedAllOracles = false;
  if (TraceIsOn("oracle-engine"))
  {
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("oracle-engine") << "---Oracle Engine Round, effort = " << e << "---"
                           << std::endl;
  }
  FirstOrderModel* fm = d_treg.getModel();
  TermDb* termDatabase = d_treg.getTermDatabase();
  eq::EqualityEngine* eq = getEqualityEngine();
  NodeManager* nm = NodeManager::currentNM();
  unsigned nquant = fm->getNumAssertedQuantifiers();
  std::vector<Node> currInterfaces;
  for (unsigned i = 0; i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i);
    if (d_qreg.getOwner(q) != this)
    {
      continue;
    }
    currInterfaces.push_back(q);
  }
  std::vector<Node> learned_lemmas;
  bool allFappsConsistent = true;
  // iterate over oracle functions
  for (const Node& f : d_oracleFuns)
  {
    std::vector<std::pair<Node, Node> > ioPairs;
    TNodeTrie* tat = termDatabase->getTermArgTrie(f);
    if (tat)
    {
      std::vector<Node> apps = tat->getLeaves(f.getType().getArgTypes().size());
      Trace("oracle-calls") << "Oracle fun " << f << " with " << apps.size()
                            << " applications." << std::endl;
      for (const auto& fapp : apps)
      {
        std::vector<Node> arguments;
        arguments.push_back(f);
        // evaluate arguments
        for (const auto& arg : fapp)
        {
          arguments.push_back(fm->getValue(arg));
        }
        // call oracle
        Node fapp_with_values = nm->mkNode(APPLY_UF, arguments);
        Node predictedResponse = eq->getRepresentative(fapp);
        ioPairs.push_back(
            std::pair<Node, Node>(fapp_with_values, predictedResponse));
      }
      if (!d_ochecker->checkConsistent(ioPairs, learned_lemmas))
      {
        allFappsConsistent = false;
      }
    }
  }
  // if all were consistent, we can terminate
  if (allFappsConsistent)
  {
    Trace("oracle-engine-state")
        << "All responses consistent, no lemmas added" << std::endl;
    d_consistencyCheckPassed = true;
  }
  else
  {
    for (const auto& l : learned_lemmas)
    {
      Trace("oracle-engine-state") << "adding lemma " << l << std::endl;
      d_qim.lemma(l, InferenceId::QUANTIFIERS_ORACLE_INTERFACE);
    }
  }
  d_checkedAllOracles = true;
  // general SMTO: call constraint generators and assumption generators here

  if (TraceIsOn("oracle-engine"))
  {
    double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("oracle-engine") << "Finished oracle engine, time = "
                           << (clSet2 - clSet) << std::endl;
  }
}

bool OracleEngine::checkCompleteFor(Node q)
{
  if (d_qreg.getOwner(q) != this)
  {
    return false;
  }
  // TODO: true if oracle consistency check works
  if (d_consistencyCheckPassed)
  {
    Trace("oracle-engine-state") << q << " is complete" << std::endl;
  }
  else
  {
    Trace("oracle-engine-state") << q << " is incomplete" << std::endl;
  }
  return d_consistencyCheckPassed;
}

void OracleEngine::checkOwnership(Node q)
{
  // take ownership of quantified formulas that are oracle interfaces
  QuantAttributes& qa = d_qreg.getQuantAttributes();
  if (qa.isOracleInterface(q))
  {
    d_qreg.setOwner(q, this, 2);
  }
}

std::string OracleEngine::identify() const
{
  return std::string("OracleEngine");
}

void OracleEngine::declareOracleFun(Node f, const std::string& binName)
{
  // TODO: set attribute propper;y
  OracleInterfaceAttribute oia;
  f.setAttribute(oia, binName);
  d_oracleFuns.push_back(f);
}

std::vector<Node> OracleEngine::getOracleFuns() const
{
  std::vector<Node> ofuns;
  for (const Node& f : d_oracleFuns)
  {
    ofuns.push_back(f);
  }
  return ofuns;
}

Node OracleEngine::mkOracleInterface(const std::vector<Node>& inputs,
                                     const std::vector<Node>& outputs,
                                     Node assume,
                                     Node constraint,
                                     const std::string& binName)
{
  Assert(!assume.isNull());
  Assert(!constraint.isNull());
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  OracleInterfaceAttribute oia;
  Node oiVar = sm->mkDummySkolem("oracle-interface", nm->booleanType());
  oiVar.setAttribute(oia, binName);
  Node ipl = nm->mkNode(INST_PATTERN_LIST, nm->mkNode(INST_ATTRIBUTE, oiVar));
  std::vector<Node> vars;
  OracleInputVarAttribute oiva;
  for (Node v : inputs)
  {
    v.setAttribute(oiva, true);
    vars.push_back(v);
  }
  OracleOutputVarAttribute oova;
  for (Node v : outputs)
  {
    v.setAttribute(oova, true);
    vars.push_back(v);
  }
  Node bvl = nm->mkNode(BOUND_VAR_LIST, vars);
  Node body = nm->mkNode(ORACLE_FORMULA_GEN, assume, constraint);
  return nm->mkNode(FORALL, bvl, body, ipl);
}
bool OracleEngine::getOracleInterface(Node q,
                                      std::vector<Node>& inputs,
                                      std::vector<Node>& outputs,
                                      Node& assume,
                                      Node& constraint,
                                      std::string& binName)
{
  QuantAttributes& qa = d_qreg.getQuantAttributes();
  if (qa.isOracleInterface(q))
  {
    // TODO: fill in data
    return true;
  }
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
