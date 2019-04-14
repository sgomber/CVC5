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

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "proof/uf_proof.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/alpha_equivalence.h"  //TODO: use
#include "theory/quantifiers/first_order_model.h"
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
      d_iexpfg(*this, qe),
      d_eqe(nullptr)
{
  d_false = NodeManager::currentNM()->mkConst(false);
  d_true = NodeManager::currentNM()->mkConst(true);
  d_eqe = new EqExplainerTe(qe->getTheoryEngine());
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
  Node q = iei.getQuantifiedFormula();
  if (d_ev.evaluate(q) != 1)
  {
    return;
  }
  if (!options::iexRegressSubsume())
  {
    // do not look at this quantified formula if it is subsumed
    // TODO: get the subsuming quantified formula.
    if (!d_qe->getModel()->isQuantifierActive(q))
    {
      return;
    }
  }
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
  std::map<int, std::unordered_set<TNode, NodeHashFunction>> visited;
  std::vector<int> visitPol;
  std::vector<TNode> visit;
  std::vector<TNode> visiti;
  /*
  bool newQuant = false;
  if (d_quants.find(q) == d_quants.end())
  {
    newQuant = true;
    d_quants[q] = true;
  }
  */

  int pol;
  //int jppol;
  TNode cur;
  TNode curi;
  visitPol.push_back(1);
  visit.push_back(q[1]);
  visiti.push_back(n);
  do
  {
    pol = visitPol.back();
    visitPol.pop_back();
    cur = visit.back();
    visit.pop_back();
    curi = visiti.back();
    visiti.pop_back();
    if (visited[pol].find(cur) == visited[pol].end())
    {
      visited[pol].insert(cur);
      Assert(cur.getKind() == curi.getKind());

      Kind k = cur.getKind();
      if (k == NOT)
      {
        visitPol.push_back(-pol);
        visit.push_back(cur[0]);
        visiti.push_back(curi[0]);
      }
      else if (k == AND || k == OR)
      {
        for (unsigned i = 0, size = cur.getNumChildren(); i < size; i++)
        {
          visitPol.push_back(pol);
          visit.push_back(cur[i]);
          visiti.push_back(curi[i]);
        }
      }
      else if (k == ITE)
      {
        for (unsigned i = 0; i < 2; i++)
        {
          visitPol.push_back(pol);
          visit.push_back(cur[i + 1]);
          visiti.push_back(curi[i + 1]);
        }
        visitPol.push_back(0);
        visit.push_back(cur[0]);
        visiti.push_back(curi[0]);
      }
      else if (k == EQUAL && cur[0].getType().isBoolean())
      {
        for (unsigned i = 0; i < 2; i++)
        {
          visitPol.push_back(0);
          visit.push_back(cur[i]);
          visiti.push_back(curi[i]);
        }
      }
      else
      {
        // a literal
        // Register the instantiation explanation information, which is used
        // to determine when this instantiation lemma will propagate.
        Node curir = curi;
        curir = Rewriter::rewrite(pol == -1 ? curir.negate() : curir);
        InstExplainLit& iel = getInstExplainLit(curir);
        iel.addInstExplanation(inst);
        Trace("inst-explain") << "  -> " << curir << std::endl;
        // also store original literals in data structure for finding TODO
        // virtual propagating instantiations
        //if (newQuant)
        //{
        //  registerPropagatingLiteral(cur, q);
        //}
        if (pol == 0)
        {
          // Store the opposite direction as well if hasPol is false,
          // since it may propagate in either polarity.
          Node curinr = Rewriter::rewrite(curi.negate());
          InstExplainLit& ieln = getInstExplainLit(curinr);
          ieln.addInstExplanation(inst);
          Trace("inst-explain") << "  -> " << curinr << std::endl;
          //if (newQuant)
          //{
          //  Node curn = cur.negate();
          //  registerPropagatingLiteral(curn, q);
          //}
        }
      }
    }
  } while (!visit.empty());
  
  // virtual proof of refutation of this instance
  std::map<Node, eq::EqProof> vrPf;
  std::vector< Node > vrPfFails;
  // make the substitution
  std::map< TNode, TNode > subs;
  for( unsigned i=0, size = ts.size(); i<size; i++ )
  {
    subs[q[0][i]] = ts[i];
  }
  TermDb * tdb = d_qe->getTermDatabase();
  bool entFalse = tdb->isEntailed(q[1], subs, false, false, vrPf, vrPfFails, true, false);
  // if we have all entailments, then we are a conflicting instance
  Trace("iex-setup") << "Instantiation led to " << vrPf.size() << " / " << (vrPf.size()+vrPfFails.size()) << " entailments." << std::endl;
  // TODO: can be more aggressive here
  if( !vrPf.empty() && vrPfFails.empty())
  {
    // go back and fill in all the proofs
    bool successPf = true;
    for (const std::pair<Node, eq::EqProof>& lit : vrPf)
    {
      // polarity is now true
      if (!tdb->isEntailed(lit.first, subs, false, true, vrPf, true))
      {
        successPf = false;
        Trace("iex-setup")
            << "...failed to reprove " << lit.first << "!" << std::endl;
        break;
      }
    }
    if( successPf )
    {
      Trace("iex-setup") << "...successfully filled in proofs." << std::endl;
      // empty proofs for the failures
      for( const Node& nc : vrPfFails )
      {
        vrPf[nc].d_node = d_null;
      }
      std::vector< Node > lemmas;
      explain(q,ts,vrPf,d_eqe,lemmas,"iex-db");
      for( const Node& lem : lemmas )
      {
        d_qe->addLemma(lem);
      }
    }
    
    // run the proof generalization procedure 
  }

  // now, propagate for future instantiations
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
                                     const char* ctx)
{
  Trace("iex") << "InstExplainDb::explain: Conflict in context " << ctx << " : "
               << std::endl;
  Trace("iex") << "  [QUANT] " << q << std::endl;

  // The virtual instantiation lemma information. This manages the information
  // regarding the conflicting instance (the base line of the proof), which
  // notice does not correspond to a registered instantiation lemma.
  InstExplainInst conflict;
  conflict.initialize(Node::null(), Node::null(), q, terms);
  // the generalization information across the conflicting literal set
  IexProof genRoot;
  genRoot.initialize(&conflict);
  // it has the conflicting quantified formula as an assumption always.
  // This is necessarily manual since genRoot is not built via an IEX inference.
  genRoot.d_assumptions.push_back(q);

  // output utility, which manages which lemmas are generated during the proof
  // generalization.
  IexOutput iout(*this);

  Assert(q.getKind() == FORALL);
  // we have that the proofs in the range of expPf are "proof sketches", i.e.
  // EqProofs whose leaves are equalities that are explanable by eqe.
  // We first regress the explanation of proofs here.
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
    Trace("iex") << "  [" << pfCounter << "] " << elit << std::endl;
    if (Trace.isOn("iex-proof-debug"))
    {
      Trace("iex-proof-debug")
          << "-----------proof (pre-regress) " << elit << std::endl;
      std::stringstream ss;
      itp->second.debug_print(ss, 1);
      Trace("iex-proof-debug") << ss.str();
      Trace("iex-proof-debug") << "-----------end proof" << std::endl;
    }
    // it may have an empty proof
    if (itp->second.d_node.isNull())
    {
      Trace("iex-proof") << "...failed to get proof" << std::endl;
      regressPfFail[elit] = true;
      // elit must be open in the generalized proof
      genRoot.setOpenConclusion(iout, elit, elit);
    }
    else if (!d_iexpfg.regressExplain(eqe, assumptions[elit], &itp->second))
    {
      Trace("iex-proof") << "...failed to regress proof" << std::endl;
      regressPfFail[elit] = true;
      // elit must be open in the generalized proof
      genRoot.setOpenConclusion(iout, elit, elit);
    }
    else
    {
      if (Trace.isOn("iex-proof"))
      {
        Trace("iex-proof") << "-----------proof " << elit << std::endl;
        std::stringstream ss;
        itp->second.debug_print(ss, 1);
        Trace("iex-proof") << ss.str();
        Trace("iex-proof") << "-----------end proof" << std::endl;
      }
    }
  }
  if (options::qcfExpMode() != QCF_EXP_GENERALIZE)
  {
    NodeManager* nm = NodeManager::currentNM();
    // If the conflict mode is not set to generalize, we just return the
    // conflict clause, which should be a Boolean conflict in the current
    // context.
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
      Trace("iex") << "InstExplainDb::explain: LEMMA regressed conflict " << lem
                   << std::endl;
      return EXP_STATUS_FULL;
    }
    else
    {
      Trace("iex") << "InstExplainDb::explain: a proof failed to regress, fail."
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
  // For example, say we found a conflicting instance justified by:
  //
  //   forall x. ~P(x) V Q(f(x,y), y)      P(a)      ~Q(f(a,b),b)
  //   ----------------------------------------------------------
  //                      false
  // In this call, expPf now contains (UF) proofs of literals P(a),
  // ~Q(f(a,b),b), which are:
  //    P(x) * sigma and ~Q(f(x,y),y) * sigma
  // where
  //    sigma is { x -> a, y -> b }
  // We call P(a), ~Q(f(a,b),b) the "ground conflicting literal set".
  //
  // The goal of proof generalization is to transform these proofs so that they
  // prove generalizations of these literals (that is, P(x) and ~Q(f(x,y),y)
  // with a subset of the substitution sigma. We say a proof is purely
  // general if it proves its literal for the empty substitution and has no
  // open leaves.
  //
  // Proofs are generalized by recognizing when assumptions of these proofs
  // are propagated (at the Boolean level) by instantiation lemmas.
  //
  // We write e.g. "P(a) / P(x)" to denote a node in a proof tree whose
  // original conclusion was P(a) and whose generalized conclusion is P(x)
  // for free (universal) variable x.
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
  // generalization of the ground conflicting instance for { x -> a }.
  //
  // Second, if there is a unique portion of the proof that is not
  // generalized and is a strict subset of the literals that comprise an
  // Inst-Explain inference (described below), then we learn the generalization
  // of this portion. We call this a (unique) propagated generalization (UPG).
  //
  // Given a (set of) generalized proofs, a "propagated generalization" is a
  // disjunction of literals corresponding to the portion of an instantiation
  // lemma that we have not generalized. For example:
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
  // where notice the propagated generalization is negated and closed in the
  // conclusion.
  //
  // If the overall proof contains a unique propagated generalization, then
  // the output of this method is a first-order hyper-resolution (for example,
  // the implication above). This additionally has the important property
  // that the quantified formula on the same line as the propagated
  // generalization is subsumed by the conclusion.
  // Above, note that:
  //   forall w. R( w )
  // subsumes
  //   forall y. Q(y) V P(y) V R(y)
  //
  // Furthermore, a conflicting instance can be generated for the propagated
  // generalization. We call this the "generalized conflicting instance". In
  // the above example, this is:
  //   forall w. R( w ) => R( a )
  // We prefer this instance to the original conflicting instance given as the
  // input to this method. (Generalized) conflicting instances are important
  // because they suffice to rule out the current ground model.

  // now go back and see if proofs can be generalized
  for (std::map<Node, eq::EqProof>::iterator itp = expPf.begin();
       itp != expPf.end();
       ++itp)
  {
    Node elit = itp->first;
    Trace("iex-gen") << "----------------- generalize proof #" << pfNum[elit]
                     << "/" << pfCounter << ": " << elit << std::endl;
    if (regressPfFail.find(elit) == regressPfFail.end())
    {
      eq::EqProof* pfp = &itp->second;
      // we can only use purely general proofs if we already have a proagating
      // generalization.
      bool reqPureGen = !genRoot.getUPGLit().isNull();
      // Below, elitg represents the ground literal appearing in the conflicting
      // literal set. Technically, elitg in fact should be set to
      //    ( elit { q[0] -> terms } )
      // but we don't bother computing this since it is not needed: we already
      // know that pfp is a proof of this literal. This term may not even appear
      // in the current context.
      Node elitg = elit;
      // We will fill the proof glc.
      IexProof& glc = genRoot.d_conclusions[elitg][elit];
      if (d_iexpfg.generalize(iout, elit, pfp, glc, reqPureGen, 1))
      {
        Trace("iex-gen") << "....success generalize, open="
                         << genRoot.isOpen(elit) << std::endl;
        if (Trace.isOn("iex-gen-debug"))
        {
          glc.debugPrint("iex-gen-debug", 2);
        }
        // glc.debugPrint("iex-gen");
        // Finalize the conclusion in the root. This either removes the proof
        // of elitg / elit and pushes its assumptions to the root, or otherwise
        // does nothing.
        genRoot.setConclusion(iout, elitg, elit);
      }
      else
      {
        // set that elitg / elit is an open leaf of the root
        genRoot.setOpenConclusion(iout, elitg, elit);
        Trace("iex-gen") << "...failed generalize" << std::endl;
      }
    }
    else
    {
      Trace("iex-gen") << "...failed to be regressed" << std::endl;
    }
    Trace("iex-gen") << "----------------- end generalize proof" << std::endl;
  }

  // now, added lemmas
  if (Trace.isOn("iex-proof"))
  {
    Trace("iex-proof") << "=== FINAL PROOF:" << std::endl;
    genRoot.debugPrint("iex-proof", 2);
    Trace("iex-proof") << "=== END FINAL PROOF" << std::endl;
  }
  // we start with d_null since the root proof is of false.
  // we denote that the proof is closed by d_false.
  genRoot.processUPG(iout, d_null, d_false);

  for (const std::pair<Node, std::vector<Node>>& sp : iout.d_subsumed_by)
  {
    for( const Node& spq : sp.second )
    {
      Trace("iex-subsume") << "InstExplainDb::subsume: " << spq << " => "
                          << sp.first << std::endl;
      d_subsume->setSubsumes(spq, sp.first);
    }
  }
  // TEMPORARY FIXME
  if (options::qcfExpGenAbort())
  {
    if (!iout.empty())
    {
      exit(77);
    }
  }
  if (iout.d_lemmas.empty())
  {
    Trace("iex") << "InstExplainDb::explain: No lemmas, fail." << std::endl;
    return EXP_STATUS_FAIL;
  }
  // add to lemmas
  lems.insert(lems.end(), iout.d_lemmas.begin(), iout.d_lemmas.end());
  Trace("iex") << "InstExplainDb::explain: generated " << lems.size()
               << " lemmas." << std::endl;
  return EXP_STATUS_FULL;
}

Node InstExplainDb::getGeneralizedConclusion(InstExplainInst* iei,
                                             const std::vector<Node>& assumps,
                                             const std::vector<Node>& concs,
                                             const std::vector<Node>& closedPremises,
                                             std::vector<Node>& lemmas,
                                             std::map<Node, std::vector<Node>>& subsumed_by,
                                             bool doGenCInst)
{
  NodeManager* nm = NodeManager::currentNM();
  Node antec = d_true;
  if (!assumps.empty())
  {
    antec = assumps.size() == 1 ? assumps[0] : nm->mkNode(AND, assumps);
  }
  Node lem;
  Node conc;
  if (!concs.empty())
  {
    // FIXME: this can be a substitution of the body instead of disjunction
    // This makes the conclusion even stronger.
    Node concBody = concs.size() == 1 ? concs[0] : nm->mkNode(OR, concs);
    
    Node q;
    // get the quantified formula if we have an InstExplainInst reference
    if (iei)
    {
      q = iei->getQuantifiedFormula();
      Assert(!q.isNull());
    }    
    
    Trace("iex-lemma-debug") << "Closed premises: " << std::endl;
    std::vector< Node > premiseVar;
    std::vector< Node > premiseSubs;
    for( const Node& cp : closedPremises )
    {
      bool pol = cp.getKind()!=NOT;
      Trace("iex-lemma-debug") << "  " << (pol ? cp : cp[0]) << " -> " << pol << std::endl;
      premiseVar.push_back(pol ? cp : cp[0]);
      // flip
      premiseSubs.push_back(pol ? d_true : d_false);
    }
    Trace("iex-lemma-debug") << "in " << (q.isNull() ? d_null : q[1]) << std::endl;
    
    Trace("iex-lemma-debug") << "(original) conclusion: " << concBody << std::endl;
    // check if we've already concluded this
    std::map<Node, Node>::iterator itpv = d_conc_cache[antec].find(concBody);
    if (itpv != d_conc_cache[antec].end())
    {
      Trace("iex-lemma-debug") << "InstExplainDb::WARNING: repeated conclusion"
                         << std::endl;
      // this can happen if a conflicting instance produces the same
      // generalization as a previous round, whereas the quantified conclusion
      // of that round did not generate the conflicting instance it could have.
      conc = itpv->second;
    }
    std::vector<Node> vars;
    if (conc.isNull())
    {
      if (q.isNull())
      {
        conc = concBody;
        Trace("iex-lemma-debug") << "construct conclusion no q: " << conc
                           << std::endl;
      }
      else
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
        Trace("iex-lemma-debug") << "construct conclusion: " << conc << std::endl;
        conc = Rewriter::rewrite(conc);
        Trace("iex-lemma-debug") << "construct conclusion post-rewrite: " << conc
                           << std::endl;
      }
      // should not have free variables, otherwise we likely have the wrong q.
      Assert(!expr::hasFreeVar(conc));
      lem = nm->mkNode(OR, antec.negate(), conc);
      std::vector< Node > casserts;
      if( conc.getKind()==OR )
      {
        // optimization: all quantified formulas in a disjunction subsume
        // if it became miniscoped after strengthening.
        for( const Node& cc : conc )
        {
          casserts.push_back(cc);
        }
      }
      else
      {
        casserts.push_back(conc);
      }
      // FIXME: could also do other subsumptions (both asserted -> subsume)
      for( const Node& cc : casserts )
      {
        if( cc.getKind()==FORALL )
        {
          // mark the subsumption
          Trace("iex-lemma-debug") << "auto-subsume: " << std::endl;
          Trace("iex-lemma-debug") << "  " << cc << " subsumes" << std::endl;
          Trace("iex-lemma-debug") << "  " << q << std::endl;
          Assert(d_subsume);
          // We are guaranteed that cc subsumes q.
          // We mark the conclusion to indicate that it deactivates
          // the original quantified formula whenever it is asserted.
          subsumed_by[q].push_back(cc);
        }
      }
      // remember that this generalization used this quantified formula
      d_conc_cache[antec][concBody] = conc;
    }
    else if (!q.isNull())
    {
      for (const Node& bv : q[0])
      {
        vars.push_back(bv);
      }
    }
    if (doGenCInst && iei)
    {
      Assert(iei->d_terms.size() == vars.size());
      // construct the generalized conflicting instance
      // notice that this bypasses the Instantiate module in QuantifiersEngine.
      // TODO: revisit this (may want to register the instantiation there)
      Node concsi = concBody.substitute(
          vars.begin(), vars.end(), iei->d_terms.begin(), iei->d_terms.end());
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
      Trace("iex-lemma") << "InstExplainDb::lemma (GEN-CINST): " << cig
                         << std::endl;
    }
  }
  else
  {
    lem = antec.negate();
    conc = d_false;
  }
  if (!lem.isNull())
  {
    Trace("iex")
        << "InstExplainDb::explain: generated generalized resolution inference"
        << std::endl;
    if (Trace.isOn("iex-lemma"))
    {
      Trace("iex-lemma") << "InstExplainDb::lemma (GEN-RES): " << lem
                         << std::endl;
      Trace("iex-lemma") << "---------------------------------" << std::endl;
      Trace("iex-lemma") << "assumptions:" << std::endl;
      if (assumps.empty())
      {
        Trace("iex-lemma") << "  (empty)" << std::endl;
      }
      else
      {
        for (const Node& a : assumps)
        {
          Trace("iex-lemma") << "  " << a << std::endl;
        }
      }
      Trace("iex-lemma") << "conclusions:" << std::endl;
      if (concs.empty())
      {
        Trace("iex-lemma") << "  (empty)" << std::endl;
      }
      else
      {
        for (const Node& c : concs)
        {
          Trace("iex-lemma") << "  " << c << std::endl;
        }
      }
      Trace("iex-lemma") << "---------------------------------" << std::endl;
    }
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
  pol = n.getKind() != NOT;
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
