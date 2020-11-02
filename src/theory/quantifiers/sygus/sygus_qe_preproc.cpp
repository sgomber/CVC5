/*********************                                                        */
/*! \file sygus_qe_preproc.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus quantifier elimination preprocessor
 **/

#include "theory/quantifiers/sygus/sygus_qe_preproc.h"

#include "expr/node_algorithm.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/single_inv_partition.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusQePreproc::SygusQePreproc(QuantifiersEngine* qe) {}

Node SygusQePreproc::preprocess(Node q)
{
  Trace("cegqi-qep") << "SygusQePreproc::preprocess: " << q << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  // decompose the conjecture into solved, unsolved components
  std::vector<Node> allf;
  std::vector<Node> unsf;
  std::map<Node, Node> solvedf;
  decomposeConjecture(q, allf, unsf, solvedf);

  // Get the functions that we would be applying single invocation for, which
  // are the functions of maximal arity having the same type.
  std::vector<Node> maxf;
  std::vector<Node> remf;
  if (!getMaximalArityFuncs(unsf, maxf, remf))
  {
    // arity mismatch for functions, we are done
    Trace("cegqi-qep") << "...max arity type mismatch, fail." << std::endl;
    return Node::null();
  }

  Trace("cegqi-qep-debug") << "Compute single invocation for " << q << "..."
                           << std::endl;
  SingleInvocationPartition sip;
  Node body = q[1];
  if (body.getKind() == NOT && body[0].getKind() == FORALL)
  {
    body = body[0][1];
  }
  sip.init(maxf, body);
  Trace("cegqi-qep-debug") << "...finished, got:" << std::endl;
  sip.debugPrint("cegqi-qep-debug");

  if (sip.isPurelySingleInvocation())
  {
    if (maxf.size() < unsf.size())
    {
      Trace("cegqi-qep") << "...eliminate functions." << std::endl;
      // solve for a subset of the functions
      Node ret = eliminateFunctions(q, allf, maxf, remf, solvedf, sip);
      Trace("cegqi-qep") << "...eliminate functions returned " << ret
                         << std::endl;
      return ret;
    }
    Trace("cegqi-qep") << "...pure single invocation, success." << std::endl;
    return Node::null();
  }

  if (!sip.isNonGroundSingleInvocation())
  {
    // property is not single invocation, fail
    Trace("cegqi-qep") << "...not non-ground single invocation, fail."
                       << std::endl;
    return Node::null();
  }
  Trace("cegqi-qep") << "...eliminate variables." << std::endl;
  // non-ground single invocation, eliminate variables
  Node ret = eliminateVariables(q, allf, maxf, remf, solvedf, sip);
  Trace("cegqi-qep") << "...eliminate variables returned " << ret << std::endl;
  return ret;
}

Node SygusQePreproc::eliminateVariables(Node q,
                                        const std::vector<Node>& allf,
                                        const std::vector<Node>& maxf,
                                        const std::vector<Node>& remf,
                                        std::map<Node, Node>& solvedf,
                                        SingleInvocationPartition& sip)
{
  NodeManager* nm = NodeManager::currentNM();
  // create new smt engine to do quantifier elimination
  std::unique_ptr<SmtEngine> smt_qe;
  initializeSubsolver(smt_qe);
  Trace("cegqi-qep-debug") << "Property is non-ground single invocation, run "
                              "QE to obtain single invocation."
                           << std::endl;
  // partition variables
  std::vector<Node> all_vars;
  sip.getAllVariables(all_vars);
  std::vector<Node> si_vars;
  sip.getSingleInvocationVariables(si_vars);
  std::vector<Node> qe_vars;
  std::vector<Node> nqe_vars;
  for (unsigned i = 0, size = all_vars.size(); i < size; i++)
  {
    Node v = all_vars[i];
    if (std::find(maxf.begin(), maxf.end(), v) != maxf.end())
    {
      Trace("cegqi-qep-debug") << "- fun var: " << v << std::endl;
    }
    else if (std::find(si_vars.begin(), si_vars.end(), v) == si_vars.end())
    {
      qe_vars.push_back(v);
      Trace("cegqi-qep-debug") << "- qe var: " << v << std::endl;
    }
    else
    {
      nqe_vars.push_back(v);
      Trace("cegqi-qep-debug") << "- non qe var: " << v << std::endl;
    }
  }
  std::vector<Node> orig;
  std::vector<Node> subs;
  // skolemize non-qe variables
  for (unsigned i = 0, size = nqe_vars.size(); i < size; i++)
  {
    Node k = nm->mkSkolem(
        "k", nqe_vars[i].getType(), "qe for non-ground single invocation");
    orig.push_back(nqe_vars[i]);
    subs.push_back(k);
    Trace("cegqi-qep-debug")
        << "  subs : " << nqe_vars[i] << " -> " << k << std::endl;
  }
  std::vector<Node> funcs1;
  sip.getFunctions(funcs1);
  for (unsigned i = 0, size = funcs1.size(); i < size; i++)
  {
    Node f = funcs1[i];
    Node fi = sip.getFunctionInvocationFor(f);
    Node fv = sip.getFirstOrderVariableForFunction(f);
    Assert(!fi.isNull());
    orig.push_back(fi);
    Node k = nm->mkSkolem(
        "k", fv.getType(), "qe for function in non-ground single invocation");
    subs.push_back(k);
    Trace("cegqi-qep-debug") << "  subs : " << fi << " -> " << k << std::endl;
  }
  // all functions are constants FIXME

  Node conj_se_ngsi = sip.getFullSpecification();
  Trace("cegqi-qep-debug") << "Full specification is " << conj_se_ngsi
                           << std::endl;
  Node conj_se_ngsi_subs = conj_se_ngsi.substitute(
      orig.begin(), orig.end(), subs.begin(), subs.end());
  Assert(!qe_vars.empty());
  conj_se_ngsi_subs = nm->mkNode(
      EXISTS, nm->mkNode(BOUND_VAR_LIST, qe_vars), conj_se_ngsi_subs.negate());

  Trace("cegqi-qep-debug") << "Run quantifier elimination on "
                           << conj_se_ngsi_subs << std::endl;
  Node qeRes = smt_qe->getQuantifierElimination(conj_se_ngsi_subs, true, false);
  Trace("cegqi-qep-debug") << "Result : " << qeRes << std::endl;

  // create single invocation conjecture, if QE was successful
  if (!expr::hasBoundVar(qeRes))
  {
    qeRes =
        qeRes.substitute(subs.begin(), subs.end(), orig.begin(), orig.end());
    if (!nqe_vars.empty())
    {
      qeRes = nm->mkNode(EXISTS, nm->mkNode(BOUND_VAR_LIST, nqe_vars), qeRes);
    }
    Assert(q.getNumChildren() == 3);
    // use mkConjecture, which carries the solved information
    qeRes = mkConjecture(allf, solvedf, qeRes, q[2]);
    Trace("cegqi-qep-debug")
        << "Converted conjecture after QE : " << qeRes << std::endl;
    qeRes = Rewriter::rewrite(qeRes);
    Node nq = qeRes;
    // must assert it is equivalent to the original
    return nq;
  }
  return Node::null();
}

Node SygusQePreproc::eliminateFunctions(Node q,
                                        const std::vector<Node>& allf,
                                        const std::vector<Node>& maxf,
                                        const std::vector<Node>& remf,
                                        std::map<Node, Node>& solvedf,
                                        SingleInvocationPartition& sip)
{
  // FIXME
  NodeManager* nm = NodeManager::currentNM();
  return Node::null();
}

void SygusQePreproc::decomposeConjecture(Node q,
                                         std::vector<Node>& allf,
                                         std::vector<Node>& unsf,
                                         std::map<Node, Node>& solvedf)
{
  Assert(q.getKind() == FORALL);
  Assert(q.getNumChildren() == 3);
  Node ipl = q[2];
  Assert(ipl.getKind() == INST_PATTERN_LIST);
  allf.insert(allf.end(), q[0].begin(), q[0].end());
  SygusSolutionAttribute ssa;
  for (const Node& ip : ipl)
  {
    if (ip.getKind() == INST_ATTRIBUTE)
    {
      Node ipv = ip[0];
      // does it specify a sygus solution?
      if (ipv.hasAttribute(ssa))
      {
        Node eq = ipv.getAttribute(ssa);
        Assert(std::find(allf.begin(), allf.end(), eq[0]) != allf.end());
        solvedf[eq[0]] = eq[1];
      }
    }
  }
  // add to unsolved functions
  for (const Node& f : allf)
  {
    if (solvedf.find(f) == solvedf.end())
    {
      unsf.push_back(f);
    }
  }
}

bool SygusQePreproc::getMaximalArityFuncs(const std::vector<Node>& unsf,
                                          std::vector<Node>& maxf,
                                          std::vector<Node>& remf)
{
  size_t maxArity = 0;
  TypeNode maxType;
  bool maxArityValid = true;
  for (const Node& f : unsf)
  {
    TypeNode tn = f.getType();
    size_t arity = tn.isFunction() ? tn.getNumChildren() - 1 : 0;
    if (arity > maxArity)
    {
      maxArityValid = true;
      maxType = tn;
    }
    else if (arity == maxArity)
    {
      if (maxType.isNull())
      {
        maxArityValid = true;
        maxType = tn;
      }
      else if (maxType != tn)
      {
        // maximal arity function is currently invalid
        maxArityValid = false;
      }
    }
  }
  if (!maxArityValid)
  {
    return false;
  }
  // deompose into maximal arity functions and remaining functions
  for (const Node& f : unsf)
  {
    TypeNode tn = f.getType();
    if (tn == maxType)
    {
      maxf.push_back(f);
    }
    else
    {
      remf.push_back(f);
    }
  }
  return true;
}

Node SygusQePreproc::mkConjecture(const std::vector<Node>& allf,
                                  const std::map<Node, Node>& solvedf,
                                  Node conj,
                                  Node ipl)
{
  Assert(!allf.empty());
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> iplChildren;
  // take existing properties, without the previous solves
  SygusSolutionAttribute ssa;
  for (const Node& ipv : ipl)
  {
    if (ipv.getKind() == INST_ATTRIBUTE && ipv[0].hasAttribute(ssa))
    {
      continue;
    }
    iplChildren.push_back(ipv);
  }
  // add the current solves, which should be a superset of the previous ones
  for (const std::pair<const Node, Node>& s : solvedf)
  {
    Node eq = s.first.eqNode(s.second);
    Node var = nm->mkSkolem("solved", nm->booleanType());
    var.setAttribute(ssa, eq);
    Node ipv = nm->mkNode(INST_ATTRIBUTE, var);
    iplChildren.push_back(ipv);
  }
  Assert(!iplChildren.empty());
  Node iplNew = nm->mkNode(INST_PATTERN_LIST, iplChildren);
  Node fbvl = nm->mkNode(BOUND_VAR_LIST, allf);
  return nm->mkNode(FORALL, fbvl, conj, iplNew);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
