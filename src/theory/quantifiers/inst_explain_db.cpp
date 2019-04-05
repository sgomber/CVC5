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
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

InstExplainDb::InstExplainDb(QuantifiersEngine* qe)
    : d_qe(qe), d_ev(d_qe->getValuation()), d_doExit(false)
{
  d_false = NodeManager::currentNM()->mkConst(false);
  d_true = NodeManager::currentNM()->mkConst(true);
}

void InstExplainDb::reset(Theory::Effort e)
{
  d_ev.reset();
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
    std::map<Node, std::vector<Node> >::iterator itw = d_waiting_prop.find(lit);
    if (itw != d_waiting_prop.end())
    {
      for (const Node& wl : itw->second)
      {
        itl->second.setPropagating(wl);
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
  if (d_active_inst.find(inst) == d_active_inst.end())
  {
    d_active_inst[inst] = true;
    InstExplainInst& iei = getInstExplainInst(inst);
    std::vector<Node> propLits;
    iei.propagate(d_ev, propLits);
    for (const Node& l : propLits)
    {
      if (l == srcLit)
      {
        src.setPropagating(inst);
      }
      else
      {
        d_waiting_prop[l].push_back(inst);
      }
    }
  }
}

void InstExplainDb::registerExplanation(Node inst,
                                        Node n,
                                        Node q,
                                        std::vector<Node>& ts)
{
  Trace("inst-explain") << "Get literals that are explanable by " << inst
                        << std::endl;
  Assert(d_inst_explains.find(inst) == d_inst_explains.end());
  InstExplainInst& iei = d_inst_explains[inst];
  iei.initialize(inst, q, ts);
  std::map<bool, std::unordered_set<Node, NodeHashFunction> > visited;
  std::vector<bool> visit_hasPol;
  std::vector<Node> visit;
  std::vector<Node> visiti;
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
        iel.addInstExplanation(inst, cur);
        Trace("inst-explain") << "  -> " << curir << std::endl;
        // Store the opposite direction as well, but if hasPol is true,
        // then we know that we will never propagate with this polarity.
        // Thus, we pass false to addInstExplanation. However, we must
        // remember where curinr came from for the purposes of explanations.
        Node curin = curi.negate();
        Node curinr = Rewriter::rewrite(curin);
        InstExplainLit& ieln = getInstExplainLit(curinr);
        ieln.addInstExplanation(inst, cur.negate(), !hasPol);
        Trace("inst-explain") << "  -> " << curinr << std::endl;
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
                                     std::vector<Node>& rexp,
                                     bool regressInst,
                                     const char* ctx)
{
  Trace("ied-conflict") << "InstExplainDb::explain: Conflict in context " << ctx << " : " << std::endl;
  Trace("ied-conflict") << "  quantified formula: " << q << std::endl;
  // we first regress the explanation of proofs
  std::map<Node, bool> regressPfFail;
  std::map<Node, std::vector<TNode> > assumptions;
  for (std::map<Node, eq::EqProof>::iterator itp = expPf.begin();
       itp != expPf.end();
       ++itp)
  {
    Node elit = itp->first;
    Trace("ied-conflict") << "  " << elit << std::endl;
    if (Trace.isOn("ied-proof-debug"))
    {
      Trace("ied-proof-debug")
          << "-----------proof (pre-regress) " << elit << std::endl;
      std::stringstream ss;
      itp->second.debug_print(ss, 1);
      Trace("ied-proof-debug") << ss.str();
      Trace("ied-proof-debug") << "-----------end proof" << std::endl;
    }
    if (!regressExplain(eqe, assumptions[elit], &itp->second))
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

  // generalized proof information
  std::map<eq::EqProof*, Node> concs;
  std::map<eq::EqProof*, std::map<Node, GLitInfo> > concsg;
  // now go back and see if proofs can be generalized
  for (std::map<Node, eq::EqProof>::iterator itp = expPf.begin();
       itp != expPf.end();
       ++itp)
  {
    Node elit = itp->first;
    Trace("ied-gen") << "----------------- generalize proof " << elit
                     << std::endl;
    if (regressPfFail.find(elit) == regressPfFail.end())
    {
      eq::EqProof* pfp = &itp->second;
      generalize(pfp, concs, concsg, 1);
      if (Trace.isOn("ied-gen"))
      {
        std::map<eq::EqProof*, std::map<Node, GLitInfo> >::iterator itg =
            concsg.find(pfp);
        if (itg != concsg.end())
        {
          // TODO
        }
      }
    }
    else
    {
      Trace("ied-gen") << "...failed to be regressed" << std::endl;
    }
    Trace("ied-gen") << "----------------- end generalize proof" << std::endl;
  }
  // We have now constructed generalizations of the proofs of all literals that
  // comprise the (ground) conflicting instance. Our goal is now to see if these
  // generalizations lead to a useful (quantified) inference.
  //
  // 
  // 
  // We introduce the following terminology.
  // 
  // Given a (set of) generalized proofs, the "propagated generalization" is a 
  // disjunction of literals corresponding to the portion of an instantiation
  // lemma that we have not explained. Here is an example:
  // 
  //                                                  forall z. ~Q(z)
  //                    --------------------------   ----------------
  // ---------------    forall y. Q(y) V P(y) V R(y)   ~Q(a) / ~Q(z)  ~R(a) / ?
  // forall x.          --------------------------------------------------------
  //  ( ~P(x) V ... )                    P(a) / P(x)               ...
  // ---------------------------------------------------------------
  //                false
  // In the above proof, ~R(a) / ~R(y) is the propagated generalization. 
  // Assuming that the remainder of the proof "..." is closed by assumptions A,
  // we have that:
  //   forall x. ~P(x) ^ forall y. Q(y) V P(y) V R(y) ^ forall z. ~Q(z) ^ A
  // implies:
  //   forall w. R( w )
  // where notice the propagated generalization is negated.
  // 
  // If the overall proof contains exactly one propagated generalization, then
  // the output of this method is a first-order hyper-resolution (as given by
  // the implication above). This additionally has the important property
  // that the quantifier on the same line as the propagated generalization is
  // subsumed by it. Above, notice that:
  //   forall w. R( w )
  // subsumes
  //   forall y. Q(y) V P(y) V R(y)
  // We mark an attribute on the conclusion to forall w. R( w ) to indicate
  // that forall y. Q(y) V P(y) V R(y) is subsumed whenever it is asserted.
  //
  // Furthermore, a conflicting instance can be generated for the propagated
  // generalization. We call this the "generalized conflicting instance". In
  // the above example, this is:
  //   forall w. R( w ) => R( a )
  // We prefer this instance to the original conflicting instance:
  //   forall x. (~P(x) V ... ) => ( ~P(a) V ... )
  
  
  // the virtual instantiation lemma
  InstExplainInst conflict;
  conflict.initialize(Node::null(), q, terms);
  // the generalization information across all literals
  GLitInfo genInfo;
  genInfo.initialize(&conflict);
  // Now, process the generalized proofs
  
  // Maps literals in the domain of our original explanation expPf to a
  // generalized conclusion (when applicable).
  std::map<Node, Node> litGeneralization;
  
  // A literal whose proof includes the "propagated generalization".
  // In the above example (EX 1), we may set litGenProp to P(x), since its proof
  // contains the propagated generalization.
  Node litGenProp;
  
  // Does the propagated generalization occur in the bottom level of the proof?
  bool litGenPropIsBase = false;
  
  for (std::map<Node, eq::EqProof>::iterator itp = expPf.begin();
       itp != expPf.end();
       ++itp)
  {
    Node elit = itp->first;
    // the propagated generalization, which begins as elit itself
    Node propGen = elit;
    // whether the proof of this literal was fully generalized
        bool pureGeneral = false;
    Trace("ied-gen") << "----------------- match generalized proof " << elit
                      << std::endl;
    if (regressPfFail.find(elit) == regressPfFail.end())
    {
      eq::EqProof* pfp = &itp->second;
      std::map<eq::EqProof*, std::map<Node, GLitInfo> >::iterator itg =
          concsg.find(pfp);
      if (itg != concsg.end())
      {
        for (const std::pair<Node, GLitInfo>& gen : itg->second)
        {
          Node genConc = convertRmEq(gen.first);
          Trace("ied-gen") << "ied-gen-match: generalizes to " << genConc << std::endl;
          // Currently, we only check whether genConc is strictly more general
          // than elit.
          if (genInfo.checkCompatible(elit, genConc, gen.second))
          {
            Trace("ied-gen") << "....success with" << std::endl;
            gen.second.debugPrint("ied-gen");
            if( gen.second.d_conclusions.empty() )
            {
              // it is a purely generalized proof (only assumptions)
              Trace("ied-gen") << "PURE, finished" << std::endl;
              litGeneralization[elit] = gen.first;
              pureGeneral = true;
              break;
            }
            else if( propGen==elit )
            {
              // set that we have a propagating generalization
              propGen = gen.first;
            }
          }
          else
          {
            Trace("ied-gen") << "...incompatible" << std::endl;
          }
        }
      }
      else
      {
        Trace("ied-gen") << "cannot match generalized proof, since no generalizations were computed"
                         << std::endl;
      }
    }
    else
    {
      Trace("ied-gen") << "cannot match generalized proof since it was not regressed" << std::endl;
    }

    // use as the propagating generalization if available
    if( !pureGeneral ) 
    {
      // Set the propagating generalization if it is available.
      // Otherwise, if the propagating generalization is not at the base level,
      // we undo the generalization of that literal.
      if( litGenProp.isNull() || ( !litGenPropIsBase && elit==propGen ) )
      {
        Trace("ied-gen") << "PROPAGATE-GENERAL " << propGen << " for " << elit << std::endl;
        if( elit==propGen )
        {
          if( !litGenPropIsBase )
          {
            Trace("ied-gen") << "...undo generalization" << std::endl;
            Assert( !litGenProp.isNull() );
            // undo the previous generalized propagation
            litGeneralization.erase(litGenProp);
          }
        }
        else
        {
          Trace("ied-gen") << "...add to generalization" << std::endl;
          // we use the generalization here
          litGeneralization[elit] = propGen;
          // elit is the literal that has the generalized propagation
          litGenProp = elit;
        }
        // the generalized propagation is in the base proof if elit is propGen
        litGenPropIsBase = (elit==propGen);
      }
    }
        Trace("ied-gen") << "----------------- end match generalized proof, gen size = " << litGeneralization.size() 
                         << std::endl;
  }
  // if we don't have useful generalizations, we fail
  if( litGeneralization.empty() )
  {
    Trace("ied-conflict") << "InstExplainDb::explain: No generalizations, fail." << std::endl;
    return EXP_STATUS_FAIL;
  }
  // now construct the inference if we have any useful generalization
  std::vector< Node > finalAssumptions;
  finalAssumptions.push_back(q);
  Node concQuant;
  std::vector< Node > finalConclusions;
  InstExplainInst* finalInfo = nullptr;
  for (std::map<Node, eq::EqProof>::iterator itp = expPf.begin();
      itp != expPf.end();
      ++itp)
  {
    Node elit = itp->first;
    std::map<Node, Node>::iterator it = litGeneralization.find(elit);
    if( it!=litGeneralization.end() )
    {
      eq::EqProof* pfp = &itp->second;
      // we generalized it, now must look up its information
      std::map<eq::EqProof*, std::map<Node, GLitInfo> >::iterator itgp =
          concsg.find(pfp);
      Assert(itgp != concsg.end());
      Node gelit = it->second;
      std::map< Node, GLitInfo>::iterator itg = itgp->second.find(gelit);
      Assert( itg!=itgp->second.end() );
      GLitInfo& ginfo = itg->second;
      if( !ginfo.d_conclusions.empty() )
      {
        // not purely general, set conclusions
        for( const std::pair<Node, std::map<Node, GLitInfo> >& cs : ginfo.d_conclusions )
        {
          for( const std::pair<Node, GLitInfo>& cc : cs.second )
          {
            finalConclusions.push_back(cc.first.negate());
            // get the instantiation lemma information about the level of the propagation
            const GLitInfo& gli = cc.second;
            InstExplainInst* glii = gli.d_iei;
            Assert( glii );
            Node qg = glii->getQuantifiedFormula();
            Assert( concQuant.isNull() || concQuant==qg );
            concQuant = qg;
            finalInfo = glii;
          }
        }
      }
      // carry all assumptions
      finalAssumptions.insert(finalAssumptions.end(),ginfo.d_assumptions.begin(),ginfo.d_assumptions.end());
    }
    else
    {
      Assert( concQuant.isNull() || concQuant==q );
      concQuant = q;
      finalConclusions.push_back(elit.negate());
      finalInfo = &conflict;
    }
  }
  // debug print the inference
  Assert( !finalAssumptions.empty() );
  if( Trace.isOn("ied-conflict") )
  {
    Trace("ied-conflict") << "Conflict explanation:" << std::endl;
    Trace("ied-conflict") << "ASSUMPTIONS:" << std::endl;
    for( const Node& fa : finalAssumptions )
    {
      Trace("ied-conflict") << "  " << fa << std::endl;
    }
    if( !finalConclusions.empty() )
    {
      Trace("ied-conflict") << "CONCLUSIONS: (from " << concQuant<< ")" << ":" << std::endl;
      for( const Node& fc : finalConclusions )
      {
        Trace("ied-conflict") << "  " << fc << std::endl;
      }
    }
    else
    {
      Trace("ied-conflict") << "CONCLUSION: false!" << std::endl;
    }
  }
  NodeManager * nm = NodeManager::currentNM();
  Node antec = d_true;
  if( !finalAssumptions.empty() )
  {
    antec = finalAssumptions.size()==1 ? finalAssumptions[0] : nm->mkNode(AND,finalAssumptions);
  }
  Node lem;
  if( !finalConclusions.empty() )
  {
    Node conc = finalConclusions.size()==1 ? finalConclusions[0] : nm->mkNode(OR,finalConclusions);
    Assert( !concQuant.isNull() );
    std::vector< Node > oldVars;
    std::vector< Node > newVars;
    for( const Node& bv : concQuant[0] )
    {
      oldVars.push_back(bv);
      Node bvn = nm->mkBoundVar(bv.getType());
      newVars.push_back(bvn);
    }
    Node concs = conc.substitute(oldVars.begin(),oldVars.end(),newVars.begin(),newVars.end());
    concs = Rewriter::rewrite(concs);
    Node bvl = nm->mkNode(BOUND_VAR_LIST,newVars);
    conc = nm->mkNode( FORALL, bvl, concs );
    conc = Rewriter::rewrite(conc);
    lem = nm->mkNode( OR, antec.negate(), conc );
    // mark the propagating generalization
    Trace("ied-conflict") << "InstExplainDb::explain: auto-subsume: " << std::endl;
    Trace("ied-conflict") << "  " << conc << " subsumes" << std::endl;
    Trace("ied-conflict") << "  " << concQuant << std::endl;
    Assert( finalInfo );
    Assert( finalInfo->getQuantifiedFormula()==concQuant );
    Assert( finalInfo->d_terms.size()==newVars.size() );
    // construct the generalized conflicting instance
    Node concsi = concs.substitute(newVars.begin(),newVars.end(),finalInfo->d_terms.begin(), finalInfo->d_terms.end() );
    Node cig = nm->mkNode( OR, conc.negate(), concsi );
    Trace("ied-conflict") << "InstExplainDb::explain: LEMMA: (generalized conflicting instance):" << std::endl;
    Trace("ied-conflict") << "  " << cig << std::endl;
    rexp.push_back(cig);
  }
  else
  {
    lem = antec.negate();
  }
  Trace("ied-conflict") << "InstExplainDb::explain: LEMMA:" << std::endl;
  Trace("ied-conflict") << "  " << lem << std::endl;
  rexp.push_back(lem);
  // FIXME
  return EXP_STATUS_FAIL;
}

void InstExplainDb::indent(const char* c, unsigned tb)
{
  for (unsigned i = 0; i < tb; i++)
  {
    Trace(c) << " ";
  }
}

bool InstExplainDb::regressExplain(EqExplainer* eqe,
                                   std::vector<TNode>& assumptions,
                                   eq::EqProof* eqp)
{
  if (eqp->d_id == eq::MERGED_THROUGH_EQUALITY)
  {
    // use the explainer
    if (eqe)
    {
      Assert(!eqp->d_node.isNull());
      Trace("ied-proof-debug") << "Explain: " << eqp->d_node << std::endl;
      if (!eqe->explain(eqp->d_node, assumptions, eqp))
      {
        Trace("ied-proof-debug") << "FAILED to explain " << eqp->d_node;
        return false;
      }
      return true;
    }
    return false;
  }
  for (unsigned i = 0, nchild = eqp->d_children.size(); i < nchild; i++)
  {
    if (!regressExplain(eqe, assumptions, eqp->d_children[i].get()))
    {
      return false;
    }
  }
  return true;
}

Node InstExplainDb::generalize(
    eq::EqProof* eqp,
    std::map<eq::EqProof*, Node>& concs,
    std::map<eq::EqProof*, std::map<Node, GLitInfo> >& concsg,
    unsigned tb)
{
  std::map<eq::EqProof*, Node>::iterator itc = concs.find(eqp);
  if (itc != concs.end())
  {
    return itc->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  // what kind of proof?
  Node ret;
  if (Trace.isOn("ied-gen"))
  {
    indent("ied-gen", tb);
  }
  unsigned id = eqp->d_id;
  if (id == eq::MERGED_THROUGH_CONGRUENCE)
  {
    Node cnode = eqp->d_node;
    Trace("ied-gen") << "ied-pf: congruence node(" << cnode << ")" << std::endl;
    // get child proofs
    std::vector<eq::EqProof*> childProofs;
    eq::EqProof* curr = eqp;
    do
    {
      Assert(curr->d_children.size() == 2);
      childProofs.push_back(curr->d_children[1].get());
      curr = curr->d_children[0].get();
    } while (curr->d_id == eq::MERGED_THROUGH_CONGRUENCE);
    unsigned nchild = cnode.getNumChildren();
    if (childProofs.size() == nchild)
    {
      bool success = true;
      std::vector<Node> rhsArgs;
      if (cnode.getMetaKind() == metakind::PARAMETERIZED)
      {
        rhsArgs.push_back(cnode.getOperator());
      }
      Node retc;
      for (unsigned i = 0; i < nchild; i++)
      {
        // child proofs are stored in reverse order since congruence proofs
        // are left associative.
        unsigned ii = nchild - (i + 1);
        retc = generalize(childProofs[ii], concs, concsg, tb + 1);
        unsigned matchIndex;
        if (getMatchIndex(retc, cnode[i], matchIndex))
        {
          rhsArgs.push_back(retc[1 - matchIndex]);
        }
        else
        {
          success = false;
          break;
        }
      }
      if (success)
      {
        Kind k = cnode.getKind();
        Node cnodeEq = nm->mkNode(k, rhsArgs);
        ret = cnode.eqNode(cnodeEq);
      }
    }
    else
    {
      Debug("ied-gen-error") << "Unexpected (cong children):" << std::endl;
      eqp->debug_print("ied-gen-error", 1);
    }
  }
  else if (id == eq::MERGED_THROUGH_EQUALITY)
  {
    // an assumption
    ret = eqp->d_node;
    Assert(ret == Rewriter::rewrite(ret));
    Trace("ied-gen") << "ied-pf: equality " << ret << std::endl;
    // try to generalize here
    std::map<Node, InstExplainLit>::iterator itl = d_lit_explains.find(ret);
    if (itl != d_lit_explains.end())
    {
      InstExplainLit& iel = itl->second;
      // activate the literal
      activateLit(ret);
      std::vector<Node>& cexp = iel.d_curr_insts;
      for (const Node& pinst : cexp)
      {
        // get the original literal
        Node olit = iel.getOriginalLit(pinst);
        Node colit = convertEq(olit);
        // initialize the generalization with the backwards mapping to its
        // concretization
        GLitInfo& gli = concsg[eqp][colit];
        if (Trace.isOn("ied-gen"))
        {
          indent("ied-gen", tb + 1);
          Trace("ied-gen") << "ied-pf: inst-explain equality " << olit
                           << std::endl;
          indent("ied-gen", tb + 1);
          Trace("ied-gen") << "        from " << pinst << std::endl;
        }
        // we must inst-explain it now
        if (!instExplain(gli, olit, ret, pinst, "ied-gen", tb + 2))
        {
          concsg[eqp].erase(colit);
          Trace("ied-gen") << "...failed" << std::endl;
        }
        else
        {
          Trace("ied-gen") << "...success!" << std::endl;
        }
      }
    }
    if (Trace.isOn("ied-gen"))
    {
      if (concsg.find(eqp) == concsg.end())
      {
        indent("ied-gen", tb + 1);
        Trace("ied-gen") << "ied-pf: no generalizations (tried "
                         << itl->second.d_curr_insts.size() << ")" << std::endl;
      }
    }
    ret = convertEq(ret);
  }
  else if (id == eq::MERGED_THROUGH_REFLEXIVITY)
  {
    // do nothing
    Node n = eqp->d_node;
    ret = n.eqNode(n);
    Trace("ied-gen") << "ied-pf: refl node(" << n << ")" << std::endl;
    // we do not care about generalizations here
  }
  else if (id == eq::MERGED_THROUGH_CONSTANTS)
  {
    //???
    Trace("ied-gen") << "ied-pf: constants ???" << std::endl;
    AlwaysAssert(false);
  }
  else if (id == eq::MERGED_THROUGH_TRANS)
  {
    Trace("ied-gen") << "ied-pf: transitivity" << std::endl;
    bool success = true;
    Node retc;
    Node r1, r2;
    for (unsigned i = 0, nproofs = eqp->d_children.size(); i < nproofs; i++)
    {
      eq::EqProof* epi = eqp->d_children[i].get();
      retc = generalize(epi, concs, concsg, tb + 1);
      if (i == 0)
      {
        r1 = retc[0];
        r2 = retc[1];
      }
      else
      {
        unsigned matchIndex;
        if (getMatchIndex(retc, r1, matchIndex))
        {
          r1 = retc[1 - matchIndex];
        }
        else if (getMatchIndex(retc, r2, matchIndex))
        {
          r2 = retc[1 - matchIndex];
        }
        else
        {
          success = false;
          break;
        }
        // FIXME: merge generalizations
      }
    }
    if (success)
    {
      ret = r1.eqNode(r2);
    }
  }
  Assert(ret.getKind() == EQUAL);
  concs[eqp] = ret;
  if (Trace.isOn("ied-gen"))
  {
    indent("ied-gen", tb);
    Trace("ied-gen") << "...proves " << ret;
    std::map<eq::EqProof*, std::map<Node, GLitInfo> >::iterator itg =
        concsg.find(eqp);
    if (itg != concsg.end())
    {
      Trace("ied-gen") << ", with " << itg->second.size() << " generalizations:" << std::endl;
      for( const std::pair< Node, GLitInfo >& p : itg->second )
      {
        indent("ied-gen", tb);
        Trace("ied-gen") << p.first << std::endl;
      }
    }
  }
  return ret;
}

bool InstExplainDb::instExplain(
    GLitInfo& g, Node olit, Node lit, Node inst, const char* c, unsigned tb)
{
  if (Trace.isOn(c))
  {
    indent(c, tb);
    Trace(c) << "INST-EXPLAIN: " << lit << " / " << olit << std::endl;
    indent(c, tb);
    Trace(c) << "         from " << inst << std::endl;
  }
  InstExplainInst& iei = getInstExplainInst(inst);
  // Since the instantiation lemma inst is propagating lit, we have that:
  //   inst { lit -> false }
  // must evaluate to false in the current context.
  Node instExp = iei.getExplanationFor(lit);

  std::vector<Node> plits;
  // Second, get the SAT literals from inst that are propagating lit.
  // These literals are such that the propositional entailment holds:
  //   inst ^ plits[0] ^ ... ^ plits[k] |= lit
  std::map<Node, bool> cache;
  if (!d_ev.propagate(instExp, cache, plits))
  {
    if (Trace.isOn(c))
    {
      indent(c, tb);
      Trace(c) << "INST-EXPLAIN FAIL: (error) could not compute Boolean "
                  "propagation based on "
               << instExp << std::endl;
    }
    // if this fails, our computation of what Boolean propagates was wrong
    Assert(false);
    return false;
  }

  // For each literal in plits, we must either regress it further, or add it to
  // the assumptions of g.
  Node q = iei.getQuantifiedFormula();
  for (const Node& pl : plits)
  {
    Assert(pl == Rewriter::rewrite(pl));
    if (Trace.isOn(c))
    {
      indent(c, tb + 1);
      Trace(c) << "inst-exp: requires " << pl << std::endl;
      indent(c, tb + 1);
    }
    // maybe it is inst-explainable
    std::map<Node, InstExplainLit>::iterator itl = d_lit_explains.find(pl);
    bool processed = false;
    if (itl != d_lit_explains.end())
    {
      InstExplainLit& iel = itl->second;
      // activate the literal
      activateLit(pl);
      std::vector<Node>& cexppl = iel.d_curr_insts;
      Trace(c) << "          ...which has " << cexppl.size()
               << " possible inst-explanations" << std::endl;
      if (!cexppl.empty())
      {
        // Get the generalization of pl with respect to the instantiation lemma
        // inst.
        Node opl = iel.getOriginalLit(inst);
        AlwaysAssert(!opl.isNull());
        if (Trace.isOn(c))
        {
          indent(c, tb + 1);
          Trace(c) << "          and generalizes to " << opl << std::endl;
        }
        // populate choices for generalization, which we store in 
        // g.d_conclusions[pl]
        for (const Node& instpl : cexppl)
        {
          // the instantiation lemma that propagates pl should not be the same
          // as the one that propagates lit
          Assert(instpl != inst);

          // check the matching constraints on opli against the original literal
          // in the quantified formula here.
          Node opli = iel.getOriginalLit(instpl);
          AlwaysAssert(!opli.isNull());
          if (Trace.isOn(c))
          {
            indent(c, tb + 2);
            Trace(c) << "inst-exp: try " << opli << "..." << std::endl;
            indent(c, tb + 2);
          }
          // currently: we avoid matching constraints altogether by only
          // pursuing generalizations that are fully compatible with the
          // current.
          if (!g.checkCompatible(opl, opli))
          {
            Trace(c) << "          ...incompatible!" << std::endl;
          }
          else
          {
            Trace(c) << "          ...compatible, recurse" << std::endl;
            // recurse
            if (!instExplain(
                    g.d_conclusions[pl][opli], opli, pl, instpl, c, tb + 3))
            {
              // undo
              g.d_conclusions[pl].erase(opli);
            }
          }
        }
        // now, take the best generalization if there are any available
        if( !g.d_conclusions[pl].empty() )
        {
          Node best;
          unsigned score = 0;
          for (const std::pair<Node, GLitInfo>& gl : g.d_conclusions[pl])
          {
            unsigned gscore = gl.second.getScore();
            if (best.isNull() || gscore > score)
            {
              best = gl.first;
              score = gscore;
            }
          }
          if (Trace.isOn(c))
          {
            indent(c, tb + 1);
            Trace(c) << "inst-exp: requires CHOOSE to merge " << best << std::endl;
            indent(c, tb + 1);
          }
          // merge the current with the child
          bool mergeSuccess = g.merge(opl, best, g.d_conclusions[pl][best]);
          // remove the conclusions
          g.d_conclusions.erase(pl);
          if (mergeSuccess)
          {
            Trace(c) << "...success" << std::endl;
          }
          else
          {
            Trace(c) << "...failed to merge choice" << std::endl;
            // we revert to the generalized form at the current level
            g.d_conclusions[pl][opl].initialize(&iei);
          }
          processed = true;
        }
        else if( Trace.isOn(c) )
        {
          indent(c, tb + 1);
          Trace(c) << "inst-exp: requires failed to generalize" << std::endl;
          indent(c, tb + 1);
        }
      }
      else if( Trace.isOn(c) )
      {
        indent(c, tb + 1);
      }
    }
    if (!processed)
    {
      if (pl != q)
      {
        // if it is not a quantified formula, then it must be part of the
        // overall conclusion
        Trace(c) << "          ...which has no inst-explanations, it must be a "
                    "conclusion"
                 << std::endl;
        // we did not generalize it at all
        g.d_conclusions[pl][pl].initialize(nullptr);
      }
      else
      {
        // if pl is the quantified formula for inst, we add it to assumptions
        Trace(c) << "          ...which is the quantified formula, add to "
                    "assumptions"
                 << std::endl;
        g.d_assumptions.push_back(pl);
      }
    }
  }
  if (Trace.isOn(c))
  {
    indent(c, tb);
    Trace(c) << "INST-EXPLAIN SUCCESS with:" << std::endl;
    g.debugPrint(c,tb+1);
  }
  return true;
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

Node InstExplainDb::convertEq(Node n)
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

Node InstExplainDb::convertRmEq(Node n)
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

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
