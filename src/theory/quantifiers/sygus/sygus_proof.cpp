/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sygus abduction utility, which transforms an arbitrary
 * input into an abduction problem.
 */

#include "theory/quantifiers/sygus/sygus_proof.h"

#include <sstream>

#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/sygus_datatype.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/smt_engine_subsolver.h"
#include "smt/set_defaults.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusProof::SygusProof(Env& env) : EnvObj(env) {}

TypeNode SygusProof::getGrammar(const std::vector<Node>& asserts)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  
  std::unordered_set<Node> symset;
  for (size_t i = 0, size = asserts.size(); i < size; i++)
  {
    expr::getSymbols(asserts[i], symset);
  }
  Trace("sygus-abduct-debug") << "Setup symbols..." << std::endl;
  
  std::unordered_set<TypeNode> allTypes;
  std::map<TypeNode, std::unordered_set<Node>> extra_cons;
  std::map<TypeNode, std::unordered_set<Node>> exclude_cons;
  std::map<TypeNode, std::unordered_set<Node>> include_cons;
  std::unordered_set<Node> terms_irrelevant;
  for (const Node& s : symset)
  {
    TypeNode tn = s.getType();
    if (tn.isDatatypeConstructor() || tn.isDatatypeSelector()
        || tn.isDatatypeTester() || tn.isDatatypeUpdater())
    {
      // datatype symbols should be considered interpreted symbols here, not
      // (higher-order) variables.
      continue;
    }
    include_cons[tn].insert(s);
  }
  std::map<TypeNode, TypeNode> = CegGrammarConstructor::mkSygusTypes(
        options(),
        allTypes,
        extra_cons,
        exclude_cons,
        include_cons);
  
  SygusDatatype sd("proof");
  
  TypeNode ptype = nm->mkUnresolvedDatatypeSort("proof");
  // add the assumptions of the grammar
  Node assumeOp = nm->mkConst(ProofOp(PfRule::ASSUME));
  for (size_t i=0, nasserts=asserts.size(); i<nasserts; i++)
  {
    Node t = nm->mkNode(PROOF, assumeOp, nasserts[0]);
    std::stringstream ss;
    ss << "dASSUME_" << i;
    sd.addConstructor(t,ss.str(),{});
  }
  // add transivity
  Node transOp = nm->mkConst(ProofOp(PfRule::TRANS));
  sd.addConstructor(transOp, "dTRANS", {ptype, ptype});
  // add unary rules
  std::vector<PfRule> unaryRules = {PfRule::SYMM,
                                  PfRule::TRUE_INTRO,
                                  PfRule::FALSE_INTRO,
                                  PfRule::TRUE_ELIM,
                                  PfRule::FALSE_ELIM};
  for (PfRule r : unaryRules)
  {
    std::stringstream ss;
    ss << "d" << r;
    Node op = nm->mkConst(ProofOp(PfRule::SYMM));
    sd.addConstructor(op, ss.str(), {ptype});
  }
  // add congruence
  
  // make the datatype
  return mkDatatypeType(sd.getDatatype());
}
  
void SygusProof::enumerateProofs(const std::string& name,
                      const std::vector<Node>& asserts)
{
  
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  
  // set up subsolver
  Options subOptions;
  subOptions.copyValues(d_env.getOptions());
  subOptions.writeQuantifiers().sygus = true;
  subOptions.writeQuantifiers().sygusStream = true;
  smt::SetDefaults::disableChecking(subOptions);
  SubsolverSetupInfo ssi(d_env, subOptions);
  initializeSubsolver(d_subSolver, ssi);

  TypeNode gtype = getGrammar(asserts);
  std::vector<Node> vars_empty;
  Node pf = nm->mkBoundVar("pf", nm->proofType());
  d_subSolver->declareSynthFun(pf, gtype, false, vars_empty);
  d_subSolver->checkSynth();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
