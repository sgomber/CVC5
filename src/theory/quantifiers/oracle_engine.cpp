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
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_tuple_enumerator.h"


#include <stdlib.h>

using namespace cvc5::kind;
using namespace cvc5::context;

namespace cvc5 {
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

OracleEngine::OracleEngine(QuantifiersState& qs,
                           QuantifiersInferenceManager& qim,
                           QuantifiersRegistry& qr,
                           TermRegistry& tr)
    : QuantifiersModule(qs, qim, qr, tr), d_oracleFuns(qs.getUserContext())
{
}

void OracleEngine::presolve() {}

// do this to play nicely
// bool InstantiationEngine::needsCheck( Theory::Effort e ){
//   return d_qstate.getInstWhenNeedsCheck(e);
// }

bool OracleEngine::needsCheck(Theory::Effort e)
{
  return e==Theory::Effort::EFFORT_LAST_CALL;
}

// the model is built at this effort level
OracleEngine::QEffort OracleEngine::needsModel(Theory::Effort e)
{
  return QEFFORT_MODEL;
}

void OracleEngine::reset_round(Theory::Effort e) {}

void OracleEngine::registerQuantifier(Node q) {}


// need to know the oracle
bool OracleEngine::checkConsistent(
  const std::vector< std::pair<Node, Node> >& ioPairs, // input-output pairs from the oracle
  std::vector<Node> &apps, std::vector<Node>& lemmas) // lemmas is to be filled, if the input-output pairs are inconsistent with model
  {
    bool consistent=true;
    NodeManager* nm = NodeManager::currentNM();
    eq::EqualityEngine* eq = getEqualityEngine();
    for(size_t i=0; i<ioPairs.size(); i++)
    {
      // get predicted result
      Node predictedResult = eq->getRepresentative(apps[i]);
      if(predictedResult!=ioPairs[i].second)
      {
        Node lemma = nm->mkNode(EQUAL,ioPairs[i].second,ioPairs[i].first);
        lemmas.push_back(lemma);
        consistent=false;
      }
    }
  return consistent;
}


void OracleEngine::check(Theory::Effort e, QEffort quant_e) {
  if(quant_e != QEFFORT_MODEL) 
    { return; }

  double clSet = 0;
  d_checkedAllOracles=false;
  if (Trace.isOn("oracle-engine"))
  {
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("oracle-engine") << "---Oracle Engine Round, effort = " << e
                         << "---" << std::endl;
  }
  FirstOrderModel* fm = d_treg.getModel();
  TermDb* termDatabase = d_treg.getTermDatabase();
  NodeManager* nm = NodeManager::currentNM();
  unsigned nquant = fm->getNumAssertedQuantifiers();
  std::vector<Node> currInterfaces;
  for (unsigned i = 0; i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i);
    if (!d_qreg.hasOwnership(q, this))
    {
      continue;
    }
    currInterfaces.push_back(q);
    if(d_callers.find(q)==d_callers.end())
    {
      d_callers.insert(std::pair<Node, OracleCaller>(q,OracleCaller(q)));
    }
    OracleCaller &caller = d_callers.at(q); 
    Trace("oracle-engine-state") << "Interface: " << q << " with binary name " << caller.getBinaryName() << std::endl;
  }
  std::vector<Node> learned_lemmas;
  bool allFappsConsistent=true;
  // iterate over oracle functions
  for (const Node& f : d_oracleFuns)
  {
    std::vector<std::pair<Node, Node> > ioPairs;
    TNodeTrie* tat = termDatabase->getTermArgTrie(f);
    if(tat)
    {
      std::vector<Node> apps = tat->getLeaves(1);
      if(d_callers.find(f)==d_callers.end())
      {
        d_callers.insert(std::pair<Node, OracleCaller>(f,OracleCaller(f)));
      }
      OracleCaller &caller = d_callers.at(f); 

      Trace("oracle-calls") << "Oracle fun "<< f <<" with binary name "<< caller.getBinaryName() 
        <<" and " << apps.size()<< " applications."<< std::endl;

      for (const auto &fapp: apps)
      {
        std::vector<Node> arguments;
        arguments.push_back(f);
        // evaluate arguments
        for(const auto &arg: fapp)
        {
          arguments.push_back(fm->getValue(arg));
        }
        // call oracle
        Node fapp_with_values = nm->mkNode(APPLY_UF, arguments);
        Node response = caller.callOracle(fapp_with_values);  
        Trace("oracle-calls") << "Node Response " << response << std::endl;
        ioPairs.push_back(std::pair<Node, Node>(fapp_with_values, response));
      }
      if(!checkConsistent(ioPairs, apps, learned_lemmas))
        allFappsConsistent=false;
    }
  }
  // if all were consistent, we can terminate
  if(allFappsConsistent)
  {
    Trace("oracle-engine-state") << "All responses consistent, no lemmas added" << std::endl;
    d_consistencyCheckPassed=true;
  }
  else
  {
    for(const auto &l: learned_lemmas)
    {
      d_qim.lemma(l, InferenceId::QUANTIFIERS_ORACLE_INTERFACE);
    }
  }  
  d_checkedAllOracles=true;
  // general SMTO: call constraint generators and assumption generators here
  
  if (Trace.isOn("oracle-engine"))
  {
    double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("oracle-engine") << "Finished oracle engine, time = "
                         << (clSet2 - clSet) << std::endl;
  }
}

bool OracleEngine::checkCompleteFor(Node q)
{
  // TODO: true if oracle consistency check works
  if(d_consistencyCheckPassed)
  {
    Trace("oracle-engine-state") << q << " is complete"<< std::endl;
  }
  else
  {
    Trace("oracle-engine-state") << q << " is incomplete"<< std::endl;
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
bool OracleEngine::getOracleInterface(Node q, std::vector<Node>& inputs,
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
}  // namespace cvc5
