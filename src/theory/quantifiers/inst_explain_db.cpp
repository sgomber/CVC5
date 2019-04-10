/*********************                                                        */
/*! \file inst_explain_db.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of instantiation explain database
 **/

#include "theory/quantifiers/inst_explain_db.h"

#include "options/quantifiers_options.h"
#include "proof/uf_proof.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/alpha_equivalence.h"  //TODO: use
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

InstExplainDb::InstExplainDb(QuantifiersEngine* qe)
    : d_qe(qe),
      d_tdb(d_qe->getTermDatabase()),
      d_subsume(d_qe->getSubsume()),
      d_ev(d_qe->getValuation()),
      d_iexpfg(*this, qe)
{
  d_false = NodeManager::currentNM()->mkConst(false);
  d_true = NodeManager::currentNM()->mkConst(true);
}

void InstExplainDb::reset(Theory::Effort e)
{
  d_ev.reset();
  d_iexpfg.reset(e);
  d_active_lexp.clear();
  d_active_inst.clear();
  d_waiting_prop.clear();
}

void InstExplainDb::activateLit(Node lit)
{
  if (d_active_lexp.find(lit) == d_active_lexp.end())
  {
    d_active_lexp[lit] = true;
    std::map<Node, InstExplainLit>::iterator itl = d_lit_explains.find(lit);
    Assert(itl != d_lit_explains.end());
    itl->second.reset();
    // add the wait list
    std::map<Node, std::vector<std::pair<Node, Node>>>::iterator itw =
        d_waiting_prop.find(lit);
    if (itw != d_waiting_prop.end())
    {
      for (const std::pair<Node, Node>& wl : itw->second)
      {
        itl->second.setPropagating(wl.first, wl.second);
      }
      d_waiting_prop.erase(lit);
    }
    // propagate for all instantiate lemmas that might propagate this literal
    for (const Node& i : itl->second.d_insts)
    {
      activateInst(i, lit, itl->second);
    }
  }
}

void InstExplainDb::activateInst(Node inst, Node srcLit, InstExplainLit& src)
{
  // check if already activated
  if (d_active_inst.find(inst) != d_active_inst.end())
  {
    return;
  }
  d_active_inst[inst] = true;
  InstExplainInst& iei = getInstExplainInst(inst);
  // it must be asserted
  if (d_ev.evaluate(iei.getQuantifiedFormula()) != 1)
  {
    return;
  }
  // check subsumed, if so, can use TODO
  std::vector<Node> lits;
  std::vector<Node> olits;
  iei.propagate(d_ev, lits, olits);
  Assert(lits.size() == olits.size());
  for (unsigned i = 0, size = lits.size(); i < size; i++)
  {
    Node l = lits[i];
    Node ol = olits[i];
    if (l == srcLit)
    {
      src.setPropagating(inst, ol);
    }
    else
    {
      d_waiting_prop[l].push_back(std::pair<Node, Node>(inst, ol));
    }
  }
}

void InstExplainDb::registerExplanation(Node inst,
                                        Node n,
                                        Node q,
                                        std::vector<Node>& ts)
{
  Assert(q.getKind() == FORALL);
  Trace("inst-explain") << "Get literals that are explanable by " << inst
                        << std::endl;
  Assert(d_inst_explains.find(inst) == d_inst_explains.end());
  InstExplainInst& iei = d_inst_explains[inst];
  iei.initialize(inst, n, q, ts);
  std::map<bool, std::unordered_set<Node, NodeHashFunction>> visited;
  std::vector<bool> visit_hasPol;
  std::vector<Node> visit;
  std::vector<Node> visiti;
  // TODO: this can be simplified to not do a parallel traversal if newQuant is
  // false.
  bool newQuant = false;
  if (d_quants.find(q) == d_quants.end())
  {
    newQuant = true;
    d_quants[q] = true;
  }
  bool hasPol;
  TNode cur;
  TNode curi;
  visit_hasPol.push_back(true);
  visit.push_back(q[1]);
  visiti.push_back(n);
  do
  {
    hasPol = visit_hasPol.back();
    cur = visit.back();
    visit.pop_back();
    curi = visiti.back();
    visiti.pop_back();
    if (visited[hasPol].find(cur) == visited[hasPol].end())
    {
      visited[hasPol].insert(cur);
      Assert(cur.getKind() == curi.getKind());

      bool pol = cur.getKind() != NOT;
      TNode atom = pol ? cur : cur[0];
      TNode atomi = pol ? curi : curi[0];
      Kind k = atom.getKind();
      if (k == AND || k == OR)
      {
        for (const Node& ac : atom)
          for (unsigned i = 0, size = atom.getNumChildren(); i < size; i++)
          {
            Node ac = atom[i];
            Node aci = atomi[i];
            visit_hasPol.push_back(hasPol);
            visit.push_back(pol ? ac : ac.negate());
            visiti.push_back(pol ? aci : aci.negate());
          }
      }
      else if (k == ITE)
      {
        for (unsigned i = 0; i < 2; i++)
        {
          Node ac = atom[i + 1];
          Node acp = pol ? ac : ac.negate();
          Node aci = atomi[i + 1];
          Node acpi = pol ? aci : aci.negate();
          visit_hasPol.push_back(hasPol);
          visit.push_back(acp);
          visiti.push_back(acpi);
        }
        visit_hasPol.push_back(false);
        visit.push_back(atom[0]);
        visiti.push_back(atomi[0]);
      }
      else if (k == EQUAL && atom[0].getType().isBoolean())
      {
        for (unsigned i = 0; i < 2; i++)
        {
          visit_hasPol.push_back(false);
          visit.push_back(atom[i]);
          visiti.push_back(atomi[i]);
        }
      }
      else
      {
        Node curir = Rewriter::rewrite(curi);
        InstExplainLit& iel = getInstExplainLit(curir);
        iel.addInstExplanation(inst);
        Trace("inst-explain") << "  -> " << curir << std::endl;
        // also store original literals in data structure for finding
        // virtual propagating instantiations
        if (newQuant)
        {
          registerPropagatingLiteral(cur, q);
        }
        if (!hasPol)
        {
          // Store the opposite direction as well if hasPol is false,
          // since it may propagate in either polarity.
          Node curinr = Rewriter::rewrite(curi.negate());
          InstExplainLit& ieln = getInstExplainLit(curinr);
          ieln.addInstExplanation(inst);
          Trace("inst-explain") << "  -> " << curinr << std::endl;
          if (newQuant)
          {
            Node curn = cur.negate();
            registerPropagatingLiteral(curn, q);
          }
        }
      }
    }
  } while (!visit.empty());
}

InstExplainLit& InstExplainDb::getInstExplainLit(Node lit)
{
  std::map<Node, InstExplainLit>::iterator itl = d_lit_explains.find(lit);
  if (itl == d_lit_explains.end())
  {
    InstExplainLit& iel = d_lit_explains[lit];
    iel.initialize(lit);
    return iel;
  }
  return itl->second;
}
bool InstExplainDb::findInstExplainLit(
    Node lit, std::map<Node, InstExplainLit>::iterator& itl)
{
  itl = d_lit_explains.find(lit);
  return itl != d_lit_explains.end();
}

InstExplainInst& InstExplainDb::getInstExplainInst(Node inst)
{
  std::map<Node, InstExplainInst>::iterator iti = d_inst_explains.find(inst);
  Assert(iti != d_inst_explains.end());
  return iti->second;
}

ExplainStatus InstExplainDb::explain(Node q,
                                     const std::vector<Node>& terms,
                                     std::map<Node, eq::EqProof>& expPf,
                                     EqExplainer* eqe,
                                     std::vector<Node>& lems,
                                     bool regressInst,
                                     const char* ctx)
{
  Trace("ied-conflict") << "InstExplainDb::explain: Conflict in context " << ctx
                        << " : " << std::endl;
  Trace("ied-conflict") << "  [QUANT] " << q << std::endl;
  Assert(q.getKind() == FORALL);
  // we first regress the explanation of proofs
  std::map<Node, bool> regressPfFail;
  std::map<Node, std::vector<TNode>> assumptions;
  unsigned pfCounter = 0;
  std::map<Node, unsigned> pfNum;
  for (std::map<Node, eq::EqProof>::iterator itp = expPf.begin();
       itp != expPf.end();
       ++itp)
  {
    pfCounter++;
    Node elit = itp->first;
    pfNum[elit] = pfCounter;
    Trace("ied-conflict") << "  [" << pfCounter << "]" << elit << std::endl;
    if (Trace.isOn("ied-proof-debug"))
    {
      Trace("ied-proof-debug")
          << "-----------proof (pre-regress) " << elit << std::endl;
      std::stringstream ss;
      itp->second.debug_print(ss, 1);
      Trace("ied-proof-debug") << ss.str();
      Trace("ied-proof-debug") << "-----------end proof" << std::endl;
    }
    if (!d_iexpfg.regressExplain(eqe, assumptions[elit], &itp->second))
    {
      Trace("ied-proof") << "...failed to regress proof" << std::endl;
      regressPfFail[elit] = true;
    }
    else
    {
      if (Trace.isOn("ied-proof"))
      {
        Trace("ied-proof") << "-----------proof " << elit << std::endl;
        std::stringstream ss;
        itp->second.debug_print(ss, 1);
        Trace("ied-proof") << ss.str();
        Trace("ied-proof") << "-----------end proof" << std::endl;
      }
    }
  }
  if (options::qcfExpMode() != QCF_EXP_GENERALIZE)
  {
    NodeManager* nm = NodeManager::currentNM();
    // we just return the conflict
    if (regressPfFail.empty())
    {
      std::vector<TNode> allAssumptions;
      for (const std::pair<Node, std::vector<TNode>>& a : assumptions)
      {
        allAssumptions.insert(
            allAssumptions.end(), a.second.begin(), a.second.end());
      }
      Assert(!allAssumptions.empty());
      allAssumptions.push_back(q);
      Node lem = nm->mkNode(AND, allAssumptions).negate();
      lems.push_back(lem);
      Trace("ied-conflict")
          << "InstExplainDb::explain: LEMMA regressed conflict " << lem
          << std::endl;
      return EXP_STATUS_FULL;
    }
    else
    {
      Trace("ied-conflict")
          << "InstExplainDb::explain: a proof failed to regress, fail."
          << std::endl;
      return EXP_STATUS_FAIL;
    }
  }

  // We now construct generalizations of the proofs of all literals that
  // comprise the (ground) conflicting instance. Our goal is now to see if these
  // generalizations lead to a useful (quantified) inference.
  //
  // In detail, given a conflicting instance, the input to this method is a
  // set of proofs of ground literals that entail a conflicting instance.
  // For example:
  //   forall x. ~P(x) V Q(f(x,y), y)      P(a)      ~Q(f(a,b),b)
  //   ----------------------------------------------------------
  //                      false
  // where expPf contains (UF) proofs of literals P(a), ~Q(f(a,b),b), which are
  //    P(x) * sigma and ~Q(f(x,y),y) * sigma
  // where
  //    sigma is { x -> a, y -> b }
  // We call P(a), ~Q(f(a,b),b) the "ground conflicting literal set" with
  // respect to forall x. ~P(x) V Q(f(x,y), y).
  //
  // The goal of proof generalization is to transform these proofs so that they
  // prove generalizations of these literals (that is, P(x) and ~Q(f(x,y),y)
  // with a subset of the substitution sigma. We say a proof is purely
  // general if it proves its literal for the empty substitution and has no
  // open leaves.
  // Proofs are generalized by recognizing when assumptions of these proofs
  // are propagated (at the Boolean level) by instantiation lemmas.
  //
  // We write e.g. "P(a) / P(x)" to denote a node in a proof tree whose
  // original conclusion was P(a) and whose generalized conclusion is P(x).
  //
  // Given proofs for all literals in a ground conflicting literal set,
  // our criteria for what consitutes a useful quantified inference is described
  // in the following,
  //
  // First, if all proofs are purely general, then we may use the generalized
  // assumptions to show false. An example would be showing that:
  //   forall x. P(x) V Q(x) ^ forall x. ~P(x) ^ forall x. ~Q(x) => false
  // when we have found conflicting instance
  //   forall x. P(x) V Q(x) => P(a) V Q(a)
  // where
  //   forall x. ~P(x), forall x. ~P(x) => ~P(a)
  //   forall x. ~Q(x), forall x. ~Q(x) => ~Q(a)
  // are asserted in the current context. This can be seen as a straightforward
  // generalization of the ground conflict for { x -> a }.
  //
  // Second, if there is a unique portion of the proof that is not
  // generalized and is a strict subset of the literals that comprise an
  // Inst-Explain inference, then we learn the generalization of this portion.
  // We call this a (unique) propagated generalization.
  //
  // Given a (set of) generalized proofs, a "propagated generalization" is a
  // disjunction of literals corresponding to the portion of an instantiation
  // lemma that we have not generalized. Here is an example:
  //
  //                                                 ---------------
  //                                                 forall z. ~Q(z)
  //                   --------------------------    --------------IEX
  // ---------------   forall y. Q(y) V P(y) V R(y)   ~Q(a) / ~Q(z)   ~R(a) / ?
  // forall x.         -----------------------------------------------------IEX
  //  ( ~P(x) V ... )                    P(a) / P(x)               ...
  // --------------------------------------------------------------IEX
  //                false
  //
  // Above, IEX denotes an "Inst-Explain" inference.
  // For example, P(a) is a conclusion of IEX since is (Boolean) propagated by
  // an instantiation lemma:
  //    forall y. Q(y) V P(y) V R(y) => Q(a) V P(a) V R(a)
  // when the above quantified formula, ~Q(a), ~R(a) are asserted in the current
  // SAT context.
  //
  // The proof of ~Q(a) is purely general via a (unit) instance of IEX.
  //
  // On the other hand, we did not generalize the proof of ~R(a).  We say that
  // ~R(a) / ~R(y) is a propagated generalization, since its proof was not
  // generalized and its literal is a strict subset of the instantiation lemma
  // above.
  //
  // Assuming that the proof "..." above is closed by assumptions A, we have
  // that ~R(a) is the *unique* propagated generalization in this proof.
  // Unique propagated generalizations lead to useful (quantified) inferences.
  // In particular, we have that:
  //   forall x. ~P(x) ^ forall y. Q(y) V P(y) V R(y) ^ forall z. ~Q(z) ^ A
  // implies:
  //   forall w. R( w )
  // where notice the propagated generalization is negated and closed.
  //
  // If the overall proof contains a unique propagated generalization, then
  // the output of this method is a first-order hyper-resolution (as given by
  // the implication above). This additionally has the important property
  // that the quantified formula on the same line as the propagated
  // generalization is subsumed by the negation of its closure.
  // Above, note that:
  //   forall w. R( w )
  // subsumes
  //   forall y. Q(y) V P(y) V R(y)
  //
  // Furthermore, a conflicting instance can be generated for the propagated
  // generalization. We call this the "generalized conflicting instance". In
  // the above example, this is:
  //   forall w. R( w ) => R( a )
  // We prefer this instance to the original conflicting instance:
  //   forall x. (~P(x) V ... ) => ( ~P(a) V ... )
  // (Generalized) conflicting instances are important because they suffice
  // to rule out the current ground model.

  // The virtual instantiation lemma information. This manages the information
  // regarding the conflicting instance (the base line of the proof), which
  // notice does not correspond to a registered instantiation lemma.
  InstExplainInst conflict;
  conflict.initialize(Node::null(), Node::null(), q, terms);
  // the generalization information across the conflicting literal set
  GLitInfo genRoot;
  genRoot.initialize(&conflict);
  // it has the conflicting quantified formula as an assumption always
  genRoot.d_assumptions.push_back(q);

  // Maps literals in the domain of our original explanation expPf to a
  // generalized conclusion that we are using (when applicable).
  std::map<Node, bool> litGeneralization;

  // A literal whose proof includes the "propagated generalization".
  // In the above example, we may set litPropGen to P(x), since its proof
  // contains the propagated generalization.
  Node litPropGen;

  // Does the propagated generalization occur in the base level of the proof?
  bool propGenIsBase = false;

  // generalized proof information
  // now go back and see if proofs can be generalized
  for (std::map<Node, eq::EqProof>::iterator itp = expPf.begin();
       itp != expPf.end();
       ++itp)
  {
    Node elit = itp->first;
    //  whether the conclusion of this leaf is on the base line of the proof
    bool concIsBase = true;
    // whether the proof of this literal was fully generalized
    bool pureGeneral = false;
    Trace("ied-gen") << "----------------- generalize proof #" << pfNum[elit]
                     << "/" << pfCounter << ": " << elit << std::endl;
    if (regressPfFail.find(elit) == regressPfFail.end())
    {
      eq::EqProof* pfp = &itp->second;
      // we can only use purely general proofs if we already have a proagating
      // generalization.
      bool reqPureGen = !litPropGen.isNull();
      // We will fill the proof glc.
      // Notice that we don't know what this proof proves currently. FIXME
      Node elitg = elit;
      GLitInfo& glc = genRoot.d_conclusions[elitg][elit];
      if( d_iexpfg.generalize(elit, pfp, glc, reqPureGen, 1) )
      {
        Trace("ied-gen") << "....success generalize with" << std::endl;
        glc.debugPrint("ied-gen");
        // Finalize the conclusion in the root. This either removes the proof
        // of elitg / elit and pushes its assumptions to the root, or otherwise
        // does nothing.
        bool setSuccess = genRoot.setConclusion(elitg,elit);
        AlwaysAssert( setSuccess );
        // did we purely generalize the proof?
        if( !genRoot.isOpen(elit))
        {
          // it is a purely generalized proof (only assumptions)
          litGeneralization[elit] = true;
          pureGeneral = true;
        }
        else
        {
          // it is a proof with a UPG
          concIsBase = false;
        }
      }
      else
      {
        Trace("ied-gen") << "...failed generalize" << std::endl;
        // add it back with no generalization
        genRoot.d_conclusions.erase(elitg);
        genRoot.d_conclusions[elitg][elit].initialize(nullptr);
      }
    }
    else
    {
      Trace("ied-gen") << "...failed to be regressed" << std::endl;
    }
    Trace("ied-gen") << "=== Compute UPG..." << std::endl;
    // use as the propagating generalization if available
    if (pureGeneral)
    {
      Trace("ied-gen") << "...purely general." << std::endl;
    }
    else
    {
      // Set the propagating generalization if it is available.
      // Otherwise, if the propagating generalization is not at the base level,
      // we undo the generalization of that literal.
      if (!litPropGen.isNull())
      {
        // if we already set a UPG, we can't use this
        concIsBase = true;
      }
      Trace("ied-gen") << "...set literal with propagated generalization to "
                       << elit << ", isBase=" << concIsBase << std::endl;
      if (concIsBase)
      {
        if (!litPropGen.isNull() && !propGenIsBase)
        {
          Trace("ied-gen") << "...undo generalization of " << litPropGen
                           << std::endl;
          // undo the previous generalized propagation
          litGeneralization.erase(litPropGen);
        }
      }
      else
      {
        Trace("ied-gen") << "...add to generalization" << std::endl;
        // we use the generalization here
        litGeneralization[elit] = true;
      }
      // elit is the literal that has the generalized propagation
      litPropGen = elit;
      // the generalized propagation is in the base proof if elit is propGen
      propGenIsBase = concIsBase;
    }
    Trace("ied-gen") << "----------------- end generalize proof" << std::endl;
  }

  // if we don't have useful generalizations, we fail.
  // This happens if and only if the propagated generalization is identical
  // to the conflicting literal set, where the conclusion of the overall
  // inference is tautological (the conflicting quantified formula implies
  // itself).
  if (litGeneralization.empty())
  {
    Trace("ied-conflict") << "InstExplainDb::explain: No generalizations, fail."
                          << std::endl;
    return EXP_STATUS_FAIL;
  }

  Trace("ied-conflict")
      << "...using " << litGeneralization.size()
      << " generalizations, a literal with propagated generalization is "
      << litPropGen << ", base=" << propGenIsBase << std::endl;

  // Now construct the inference if we have any useful generalization.
  std::vector<Node> finalAssumptions;
  finalAssumptions.insert(finalAssumptions.end(),genRoot.d_assumptions.begin(),genRoot.d_assumptions.end());
  Node concQuant;
  std::vector<Node> finalConclusions;
  InstExplainInst* finalInfo = nullptr;
  for (std::map<Node, eq::EqProof>::iterator itp = expPf.begin();
       itp != expPf.end();
       ++itp)
  {
    Node elit = itp->first;
    std::map<Node, bool>::iterator it = litGeneralization.find(elit);
    if (it != litGeneralization.end())
    {
      Node elitg = elit;
      if( genRoot.isOpen(elitg) )
      {
        // we generalized it, now must look up its information
        std::map<Node, GLitInfo>::iterator itgp = genRoot.d_conclusions[elitg].find(elit);
        Assert(itgp != genRoot.d_conclusions[elitg].end());
        // get the UPG information from this
        InstExplainInst* iei =
            itgp->second.getUPG(finalConclusions, concQuant, finalAssumptions);
        if (iei)
        {
          Assert(!finalInfo);
          finalInfo = iei;
        }
      }
    }
    else
    {
      Assert(concQuant.isNull() || concQuant == q);
      concQuant = q;
      finalConclusions.push_back(elit.negate());
      finalInfo = &conflict;
    }
  }
  // debug print the inference
  Assert(!finalAssumptions.empty());
  if (Trace.isOn("ied-conflict"))
  {
    Trace("ied-conflict") << "Conflict explanation:" << std::endl;
    Trace("ied-conflict") << "ASSUMPTIONS:" << std::endl;
    for (const Node& fa : finalAssumptions)
    {
      Trace("ied-conflict") << "  " << fa << std::endl;
    }
    if (!finalConclusions.empty())
    {
      Trace("ied-conflict") << "CONCLUSIONS: (from " << concQuant << ")"
                            << ":" << std::endl;
      for (const Node& fc : finalConclusions)
      {
        Trace("ied-conflict") << "  " << fc << std::endl;
      }
    }
    else
    {
      Trace("ied-conflict") << "CONCLUSION: false!" << std::endl;
    }
  }
  getGeneralizedConclusion(finalInfo, finalAssumptions, finalConclusions, lems);
  // TEMPORARY FIXME
  if (options::qcfExpGenAbort())
  {
    exit(77);
  }
  return EXP_STATUS_FULL;
}

Node InstExplainDb::getGeneralizedConclusion(InstExplainInst* iei, const std::vector< Node >& assumps, const std::vector< Node >& concs, std::vector< Node >& lemmas )
{
  NodeManager* nm = NodeManager::currentNM();
  Node antec = d_true;
  if (!assumps.empty())
  {
    antec = assumps.size() == 1 ? assumps[0]
                                         : nm->mkNode(AND, assumps);
  }  
  Node lem;
  Node conc;
  Assert( iei );
  if (!concs.empty())
  {
    Node concBody = concs.size() == 1
                        ? concs[0]
                        : nm->mkNode(OR, concs);
    Trace("ied-conflict-debug")
        << "(original) conclusion: " << conc << std::endl;
    // check if we've already concluded this
    std::map<Node, Node>::iterator itpv = d_conc_cache[antec].find(concBody);
    if (itpv != d_conc_cache[antec].end())
    {
      Trace("ied-conflict-debug")
          << "InstExplainDb::WARNING: repeated conclusion" << std::endl;
      // this can happen if a conflicting instance produces the same
      // generalization as a previous round, whereas the quantified conclusion
      // of that round did not generate the conflicting instance it could have.
      conc = itpv->second;
    }
    Node q = iei->getQuantifiedFormula();
    Assert(!q.isNull());
    std::vector<Node> vars;
    if (conc.isNull())
    {
      std::vector<Node> newVars;
      for (const Node& bv : q[0])
      {
        vars.push_back(bv);
        Node bvn = nm->mkBoundVar(bv.getType());
        newVars.push_back(bvn);
      }
      Node concsubs = concBody.substitute(
          vars.begin(), vars.end(), newVars.begin(), newVars.end());
      concsubs = Rewriter::rewrite(concsubs);
      Node bvl = nm->mkNode(BOUND_VAR_LIST, newVars);
      conc = nm->mkNode(FORALL, bvl, concsubs);
      conc = Rewriter::rewrite(conc);
      lem = nm->mkNode(OR, antec.negate(), conc);
      // mark the propagating generalization
      Trace("ied-conflict-debug") << "auto-subsume: " << std::endl;
      Trace("ied-conflict-debug") << "  " << conc << " subsumes" << std::endl;
      Trace("ied-conflict-debug") << "  " << q << std::endl;
      Assert(d_subsume);
      // We are guaranteed that conc subsumes q.
      // We mark the conclusion to indicate that it deactivates
      // the original quantified formula whenever it is asserted.
      d_subsume->setSubsumes(conc, q);
      d_conc_cache[antec][concBody] = conc;
    }
    else
    {
      for (const Node& bv : q[0])
      {
        vars.push_back(bv);
      }
    }
    Assert(iei);
    Assert(iei->d_terms.size() == vars.size());
    // construct the generalized conflicting instance
    // notice that this bypasses the Instantiate module in QuantifiersEngine.
    // TODO: revisit this (may want to register the instantiation there)
    Node concsi = concBody.substitute(vars.begin(),
                                      vars.end(),
                                      iei->d_terms.begin(),
                                      iei->d_terms.end());
    Node cig = nm->mkNode(OR, conc.negate(), concsi);
    cig = Rewriter::rewrite(cig);
    // already register the explanation
    if (conc.getKind() == FORALL)
    {
      // we guard whether conc is a FORALL for the rare case where conc is
      // rewritten to a non-quantifier (e.g. via miniscoping or variable
      // elimination).
      registerExplanation(cig, concsi, conc, iei->d_terms);
    }
    lemmas.push_back(cig);
    Trace("ied-lemma") << "InstExplainDb::lemma (GEN-CINST): " << cig
                       << std::endl;
  }
  else
  {
    lem = antec.negate();
    conc = d_false;
  }
  if (!lem.isNull())
  {
    Trace("ied-conflict")
        << "InstExplainDb::explain: generated generalized resolution inference"
        << std::endl;
    Trace("ied-lemma") << "InstExplainDb::lemma (GEN-RES): " << lem
                       << std::endl;
    lemmas.push_back(lem);
  }
  return conc;
}

void InstExplainDb::indent(const char* c, unsigned tb)
{
  for (unsigned i = 0; i < tb; i++)
  {
    Trace(c) << " ";
  }
}

bool InstExplainDb::getMatchIndex(Node eq, Node n, unsigned& index)
{
  if (eq.isNull())
  {
    return false;
  }
  Assert(eq.getKind() == EQUAL);
  for (unsigned i = 0; i < 2; i++)
  {
    if (eq[i] == n)
    {
      index = i;
      return true;
    }
  }

  return false;
}

Node InstExplainDb::convertEq(Node n) const
{
  Kind k = n.getKind();
  if (k == EQUAL)
  {
    return n;
  }
  else if (k == NOT)
  {
    return n.eqNode(d_false);
  }
  Assert(n.getType().isBoolean());
  return n.eqNode(d_true);
}

Node InstExplainDb::convertRmEq(Node n) const
{
  Assert(n.getKind() == EQUAL);
  if (n[1] == d_true)
  {
    return n[0];
  }
  else if (n[1] == d_false)
  {
    n[0].negate();
  }
  return n;
}

bool InstExplainDb::isGeneralization(Node n, Node gn)
{
  // TODO
  return true;
}

void InstExplainDb::registerPropagatingLiteral(Node olit, Node q)
{
  bool pol;
  Node f, g;
  if (!getLitSymbolIndex(olit, f, g, pol))
  {
    // the literal is not indexable
    return;
  }
  // otherwise, add to database
  d_plit_map[f][g][pol].push_back(olit);
}
bool InstExplainDb::getLitSymbolIndex(Node n, Node& f, Node& g, bool& pol) const
{
  pol = n.getKind() == NOT;
  TNode atom = pol ? n : n[0];
  // we index by the equality f(t[x]) = g(s[x]) that this is equivalent to,
  // where f <= g by node comparison
  if (atom.getKind() != EQUAL)
  {
    f = d_tdb->getMatchOperator(atom);
    if (f.isNull())
    {
      return false;
    }
    return true;
  }
  for (unsigned i = 0; i < 2; i++)
  {
    Node op;
    if (atom[i].getKind() != BOUND_VARIABLE)
    {
      op = d_tdb->getMatchOperator(atom[i]);
      if (op.isNull())
      {
        return false;
      }
    }
    if (i == 0)
    {
      f = op;
    }
    else if (op < f)
    {
      // if node comparison, swap
      g = f;
      f = op;
    }
    else
    {
      g = op;
    }
  }
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
