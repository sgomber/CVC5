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
#include <iostream>

using namespace cvc5::kind;
using namespace cvc5::context;

bool is_digits(const std::string &str)
{
    return str.find_first_not_of("0123456789") == std::string::npos;
}

namespace cvc5 {
namespace theory {
namespace quantifiers {

Node OracleEngine::get_hex_numeral(std::string in)
{
  // we accept any sequence of '0'-'9', 'a'-'f', 'A'-'F'
  std::size_t width = in.size()*16;
  NodeManager* nm = NodeManager::currentNM();
  unsigned int val = std::stoi(in, nullptr, 16);
  Node result =  nm->mkConst(BitVector(width,val));
  return result;
}

Node OracleEngine::get_bin_numeral(std::string in)
{
  // we accept any sequence of '0'-'1'
  std::size_t width = in.size();
  NodeManager* nm = NodeManager::currentNM();
  unsigned int val = std::stoi(in, nullptr, 2);
  Node result = nm->mkConst(BitVector(width,val));
  return result;
}

Node OracleEngine::get_dec_numeral(std::string in)
{
  // we accept any sequence of '0'-'9'
  NodeManager* nm = NodeManager::currentNM();
  unsigned int val = std::stoi(in, nullptr, 10);
  Node result  = nm->mkConst(Rational(val));
  return result;
}

Node OracleEngine::responseParser(std::string &in)
{
  // Assumes the response is a singular integer or bitvector literal
  // Temporary: will eventually be replaced with some subcomponent of full parser
  NodeManager* nm = NodeManager::currentNM();
  if(in.at(0)=='#')
  {
    if(in.at(1)=='b')
      return get_bin_numeral(in);
    else if(in.at(1)=='x')
      return get_hex_numeral(in);
    else
      Assert(0); // throw error here
  }
  else if(is_digits(in))
    return get_dec_numeral(in);
  else if(in.find("true")!=std::string::npos)
  {
    Node result = nm->mkConst(true);
    return result;
  }
  else if(in.find("false")!=std::string::npos)
  {
    Node result = nm->mkConst(false);
    return result;
  }
  else
    Assert(0); // throw error here
}


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

std::string OracleEngine::getBinaryName(const Node n)
{
  // oracle functions have no children
  if(n.getNumChildren()<3)
    return n.getAttribute(OracleInterfaceAttribute());

  // oracle interfaces have children, and the attribute is stored in 2nd child 
  for (const Node& v : n[2][0]) 
  { 
    if(v.getAttribute(OracleInterfaceAttribute())!="")
      return v.getAttribute(OracleInterfaceAttribute());
  }
  return "";
} 



Node OracleEngine::callOracle(const std::string &binary_name, 
                                     const std::vector<Node> &argv)
{
  Trace("oracle-calls") << "Running oracle: " << binary_name ;
  std::vector<std::string> string_args;
  for (auto &arg : argv)
  {
    std::ostringstream oss;
    oss << arg;
    string_args.push_back(oss.str());
    Trace("oracle-calls") << ' ' << arg;
  }
  Trace("oracle-calls") << std::endl;

  // run the oracle binary
  std::ostringstream stdout_stream;

  auto run_result = run(
      binary_name,
      string_args,
      "",
      stdout_stream,
      "");

  // we assume that an oracle has a return code of 0 or 10. 
  if (run_result != 0 && run_result !=10)
  {
    Trace("oracle-calls") << "oracle " << binary_name << " has failed with exit code " << run_result << std::endl;
    Assert(run_result==0 || run_result==10);
  }
  // we assume that the oracle returns the result in SMT-LIB format
  std::string stringResponse = stdout_stream.str();
  // parse response into a Node
  return responseParser(stringResponse);
}

void OracleEngine::check(Theory::Effort e, QEffort quant_e) {
  double clSet = 0;
  checkedAllOracles=false;
  if (Trace.isOn("oracle-engine"))
  {
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("oracle-engine") << "---Oracle Engine Round, effort = " << e
                         << "---" << std::endl;
  }
  FirstOrderModel* fm = d_treg.getModel();
  TermDb* termDatabase = d_treg.getTermDatabase();
  eq::EqualityEngine* eq = getEqualityEngine();
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
    Trace("oracle-engine-state") << "Interface: " << q << " with binary name " << getBinaryName(q) << std::endl;
  }
  bool all_fapps_consistent=true;
  std::vector<Node> learned_lemmas;
  // iterate over oracle functions
  for (const Node& f : d_oracleFuns)
  {
    TNodeTrie* tat = termDatabase->getTermArgTrie(f);
    if(tat)
    {
      std::vector<Node> apps = tat->getLeaves(1);
      std::string binaryName = getBinaryName(f);
      Trace("oracle-calls") << "Oracle fun "<< f <<" with binary name "<< binaryName 
        <<" and " << apps.size()<< " applications."<< std::endl;
  
      // get applications of oracle function
      // iterate over applications
      for (const auto &fapp: apps)
      {
        Trace("oracle-calls") << "Oracle app: " << fapp << ", ";
        std::vector<Node> arguments;
        arguments.push_back(f);
        // evaluate arguments
        for(const auto &arg: fapp)
        {
          arguments.push_back(fm->getValue(arg));
          // arguments.push_back(eq->getRepresentative(arg));
          Trace("oracle-calls") << "Arg: " << arg << ", value " << fm->getValue(arg) <<
          ", representation "<< eq->getRepresentative(arg)<< std::endl;
        }

        // call oracle
        Node response = callOracle(binaryName, arguments);  
        Trace("oracle-calls") << "Node Response " << response;
        NodeManager* nm = NodeManager::currentNM();
        // check consistency with model
        Node predictedResult = eq->getRepresentative(fapp);
        Trace("oracle-calls") << ", expected " << predictedResult << std::endl;

        if(predictedResult!=response)
        {
          Trace("oracle-calls") << "Inconsistent response! Model expected " << predictedResult << std::endl;
          all_fapps_consistent=false;
        }
        // add lemma
        Node fapp_with_values = nm->mkNode(APPLY_UF, arguments);
        Node lemma = nm->mkNode(EQUAL,response,fapp_with_values);
        learned_lemmas.push_back(lemma);
      }
    }
  }
  // if all were consistent, we can terminate
  if(all_fapps_consistent)
  {
    Trace("oracle-engine-state") << "All responses consistent, no lemmas added" << std::endl;
    consistencyCheckPassed=true;
  }
  else
  {
    for(const auto &l: learned_lemmas)
    {
      // Trace("oracle-engine-state") << "Adding lemma " << l << std::endl;
      d_qim.lemma(l, InferenceId::QUANTIFIERS_ORACLE_INTERFACE);
    }
  }  
  checkedAllOracles=true;
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
  if(consistencyCheckPassed)
    Trace("oracle-engine-state") << q << " is complete"<< std::endl;
  else
    Trace("oracle-engine-state") << q << " is incomplete"<< std::endl;
  return consistencyCheckPassed;
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
