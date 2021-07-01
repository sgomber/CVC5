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
#include "util/run.h"

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

bool OracleEngine::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void OracleEngine::reset_round(Theory::Effort e) {}

void OracleEngine::registerQuantifier(Node q) {}

std::string OracleEngine::callOracle(const std::string &binary_name, 
                                     const std::vector<std::string> &argv)
{
  Trace("oracle-engine") << "Running oracle: " << binary_name;
  for (auto &arg : argv)
    Trace("oracle-engine") << ' ' << arg;
  Trace("oracle-engine") << std::endl;

  // run the oracle binary
  std::ostringstream stdout_stream;

  auto run_result = run(
      binary_name,
      argv,
      "",
      stdout_stream,
      "");

  // we assume that an oracle has a return code of 0 or 10. 
  if (run_result != 0 && run_result !=10)
  {
    Trace("oracle-engine") << "oracle " << binary_name << " has failed with exit code " << run_result << std::endl;
    Assert(run_result==0 || run_result==10);
  }
  // we assume that the oracle returns the result in SMT-LIB format
  std::istringstream oracle_response_istream(stdout_stream.str());
  Trace("oracle-engine") << "Oracle response is "<< stdout_stream.str() << std::endl;
  return stdout_stream.str();
}

void OracleEngine::check(Theory::Effort e, QEffort quant_e) {
  double clSet = 0;
  if (Trace.isOn("oracle-engine"))
  {
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("oracle-engine") << "---Oracle Engine Round, effort = " << e
                         << "---" << std::endl;
  }
  FirstOrderModel* fm = d_treg.getModel();
  // TermDb* termDatabase = d_treg.getTermDatabase();
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
    Trace("oracle-engine-state") << "Interface: " << q << std::endl;
  }

  // iterate over oracle functions
  for (const Node& f : d_oracleFuns)
  {
    Trace("oracle-engine-state") << "Oracle fun: " << f << std::endl;
    // get applications of oracle function
    // iterate over applications
    // evaluate arguments
    // call oracle
    // get response
    // check consistency with model
    // add lemma
  }
  // if all were consistent, we can terminate

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
  return false;
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

void OracleEngine::declareOracleFun(Node f) { d_oracleFuns.push_back(f); }

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
