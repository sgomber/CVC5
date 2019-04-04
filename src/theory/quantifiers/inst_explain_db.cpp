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
        iel.addInstExplanation(inst, curi, cur);
        Trace("inst-explain") << "  -> " << curir << std::endl;
        if (!hasPol)
        {
          Node curin = curi.negate();
          Node curinr = Rewriter::rewrite(curin);
          InstExplainLit& ieln = getInstExplainLit(curinr);
          ieln.addInstExplanation(inst, curin, cur.negate());
          Trace("inst-explain") << "  -> " << curinr << std::endl;
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

InstExplainInst& InstExplainDb::getInstExplainInst(Node inst)
{
  std::map<Node, InstExplainInst>::iterator iti = d_inst_explains.find(inst);
  Assert(iti != d_inst_explains.end());
  return iti->second;
}

ExplainStatus InstExplainDb::explain(Node q,
                                     const std::vector< Node >& terms,
                                     std::map< Node, eq::EqProof >& expPf,
                                     EqExplainer* eqe,
                                     std::vector<Node>& rexp,
                                     bool regressInst,
                                     const char* ctx)
{
  ExplainStatus ret = EXP_STATUS_FAIL;
  Trace("ied-conflict") << "Conflict in context " << ctx << " : " << std::endl;
  Trace("ied-conflict") << "  quantified formula: " << q << std::endl;
  // we first regress the explanation of proofs
  std::map< Node, bool > regressPfFail;
  std::map< Node, std::vector< TNode > > assumptions;
  for( std::map< Node, eq::EqProof >::iterator itp = expPf.begin(); itp != expPf.end(); ++itp )
  {
    Node elit = itp->first;
    Trace("ied-conflict") << "  " << elit << std::endl;
    if( Trace.isOn("ied-proof-debug") )
    {
      Trace("ied-proof-debug") << "-----------proof (pre-regress) " << elit << std::endl;
      std::stringstream ss;
      itp->second.debug_print(ss, 1);
      Trace("ied-proof-debug") << ss.str();
      Trace("ied-proof-debug") << "-----------end proof" << std::endl;
    }
    if( !regressExplain(eqe, assumptions[elit],&itp->second) )
    {
      regressPfFail[elit] = true;
    }
    if( Trace.isOn("ied-proof") )
    {
      Trace("ied-proof") << "-----------proof " << elit << std::endl;
      std::stringstream ss;
      itp->second.debug_print(ss, 1);
      Trace("ied-proof") << ss.str();
      Trace("ied-proof") << "-----------end proof" << std::endl;
    }
  }

  // generalized proof information
  std::map<eq::EqProof*, Node> concs;
  std::map<eq::EqProof*, std::map<Node, GLitInfo> > concsg;
  // now go back and see if proofs can be generalized
  for( std::map< Node, eq::EqProof >::iterator itp = expPf.begin(); itp != expPf.end(); ++itp )
  {
    Node elit = itp->first;
    if( regressPfFail.find(elit)!=regressPfFail.end() )
    {
      eq::EqProof * pfp = &itp->second;
      Trace("ied-gen") << "----------------- generalize proof " << elit << std::endl;
      generalize(pfp, concs, concsg, 1);
      if( Trace.isOn("ied-gen") )
      {
        std::map<eq::EqProof*, std::map<Node, GLitInfo> >::iterator itg = concsg.find(pfp);
        if( itg != concsg.end() )
        {
          // TODO
        }
        Trace("ied-gen") << "----------------- end generalize proof" << std::endl;
      }
    }
    else
    {
      Trace("ied-gen") << "----------------- cannot generalize proof " << elit << ", which failed to be regressed" << std::endl;
    }
  }
  
  // the virtual instantiation lemma
  InstExplainInst conflict;
  conflict.initialize(q,Node::null(),terms);
  // the generalization information across all literals
  GLitInfo genInfo;
  genInfo.initialize(&conflict);
  
  // now, process the generalized proofs
  // the literals whose proofs were fully generalized
  std::map< Node, bool > litFullRegress;
  for( std::map< Node, eq::EqProof >::iterator itp = expPf.begin(); itp != expPf.end(); ++itp )
  {
    Node elit = itp->first;
    if( regressPfFail.find(elit)!=regressPfFail.end() )
    {
      eq::EqProof * pfp = &itp->second;
      std::map<eq::EqProof*, std::map<Node, GLitInfo> >::iterator itg = concsg.find(pfp);
      if( itg != concsg.end() )
      {
        Trace("ied-gen") << "----------------- match generalized proof " << elit << std::endl;
        for( const std::pair< Node, GLitInfo >& gen : itg->second ) 
        {
          Node genConc = convertRmEq(gen.first);
          Trace("ied-gen") << "ied-gen-match: Try " << genConc << std::endl;
          // Currently, we only check whether genConc is strictly more general
          // than elit.
          if( genInfo.checkCompatible( elit, genConc, gen.second ) )
          {
            Trace("ied-gen") << "ied-gen-match: SUCCESS" << std::endl;
            litFullRegress[elit] = true;
            break;
          }
        }
        Trace("ied-gen") << "----------------- end match generalized proof " << std::endl;
      }
      else
      {
        Trace("ied-gen") << "----------------- cannot match generalized proof " << elit << ", since no generalizations were computed" << std::endl;
      }
    }
    else
    {
      Trace("ied-gen") << "----------------- cannot match generalized proof " << elit << std::endl;
    }
  }
  
  
  
/*
  std::map<Node, bool> expres;
  std::map<Node, bool> expresAtom;

  // Possible generalized assumptions  FIXME doc
  // Each of these should be such that:
  //    for all i: gassumptions[i] * subs = assumptions[i]
  // And be such that:
  //    g_1 ^ ... ^ g_n => ge
  // where g_j in gassumptions[i][j] for j = 1, ... n.
  // In other words, these represent a generalization of the proof of:
  //    assumptions[i] ^ ... ^ assumptions[i] => e
  std::map<TNode, TNode > gassumptions;
  
  
  for (unsigned i = 0, esize = exp.size(); i < esize; i++)
  {
    Node e = exp[i];
    Node ge = gexp[i];
    Assert( isGeneralization(e,ge) );
    Node er = Rewriter::rewrite(e);
    Node ger = Rewriter::rewrite(e);
    // Cache based on the generalizations
    if (proc_pre.find(ger) != proc_pre.end())
    {
      continue;
    }
    proc_pre[ger] = true;

    // Compute the rewritten generalization: ensure that matching is maintained
    if (e == er)
    {
      ger = ge;
    }
    else
    {
      bool erpol = er.getKind() != NOT;
      Node erAtom = erpol ? er : er[0];
      // may have flipped via symmetry
      if (erAtom.getKind() == EQUAL)
      {
        if (er[0] == e[1] && er[1] == e[0])
        {
          ger = ge[1].eqNode(ge[0]);
          ger = erpol ? ger : ger.negate();
        }
      }
    }
    if( ger.isNull() )
    {
      // shouldn't happen currently
      Assert(false);
      // drop ger (fix its free variables)
      genInfo.drop(ger);
      continue;
    }
    Assert( isGeneralization(er,ger) );
    bool regressExp = false;
    std::shared_ptr<eq::EqProof> pf = nullptr;
    bool processedGenExp = false;  
    std::vector< TNode > currAssumptions;
    // first, regress the explanation using the eqe utility
    if (eqe)
    {
      // TODO now, go back and regress all the leaves of the proof sketch
      
      
      
      // TODO: shortcut case where trivially holds via SAT value?

      pf = std::make_shared<eq::EqProof>();
      Trace("ied-conflict-debug") << "Explain: " << er << std::endl;
      if (eqe->explain(er, currAssumptions, pf.get()))
      {
        regressExp = true;
        Trace("ied-conflict-debug")
            << "  ...regressed to " << currAssumptions << std::endl;
        if (Trace.isOn("ied-proof"))
        {
          Trace("ied-proof") << "-----------proof of " << er << std::endl;
          std::stringstream ss;
          pf->debug_print(ss, 1);
          Trace("ied-proof") << ss.str();
          Trace("ied-proof") << "-----------end proof" << std::endl;
        }
        // compute the generalized assumptions
        Trace("ied-gen") << "ied-pf: generalize: " << er << std::endl;
        Trace("ied-gen") << "ied-pf:     target: " << ger << std::endl;
        eq::EqProof * pfp = pf.get();
        std::map<eq::EqProof*, Node> concs;
        std::map<eq::EqProof*, std::map<Node, GLitInfo> > concsg;
        generalize(er, ger, pfp, concs, concsg, 1);
        std::map<eq::EqProof*, std::map<Node, GLitInfo> >::iterator itg = concsg.find(pfp);
        if( itg != concsg.end() )
        {
          for( const std::pair< Node, GLitInfo >& gen : itg->second ) 
          {
            Node genConc = convertRmEq(gen.first);
            Trace("ied-gen") << "ied-pf: gen-result: " << genConc << std::endl;
            // merge the generalizations based on matching
            if( genInfo.merge( ger, genConc, gen.second ) )
            {
              // just take the first that works
              processedGenExp = true;
              // copy to gassumptions
              for( const std::pair< TNode, TNode >& gp : gen.second.d_reqInstExplains )
              {
                gassumptions[gp.first] = gp.second;
              }
              break;
            }
          }
        }
      }
      else
      {
        Trace("ied-conflict-debug") << "  ...failed to regress" << std::endl;
      }
    }
    if( !processedGenExp )
    {
      // if we didn't process the generalized explanation
      genInfo.drop(ger);
    }
    if (!regressExp)
    {
      currAssumptions.push_back(er);
      // it might be inst-explainable?
      
      // if we did not explain it, then we need to set the status
      // however, we could still hope that this assertion simply holds in the
      // current context
      // ret = EXP_STATUS_INCOMPLETE;
    }
    // carry the assumptions 
    assumptions.insert(assumptions.end(),currAssumptions.begin(),currAssumptions.end());
  }
  */
/*
    // for (TNode ert : assumptions)
    for (unsigned i = 0, asize = assumptions.size(); i < asize; i++)
    {
      Node a = assumptions[i];
      // now, regress the equality in terms of instantiation lemmas
      Assert(Rewriter::rewrite(a) == a);
      Trace("ied-conflict-debug") << "*** " << a << std::endl;
      if (regressInst)
      {
        instExplain(a, expres, expresAtom, regressInst);
      }
      else
      {
        expresAtom[a] = true;
      }
    }
  // now, we go back and inst-explain those that we generalized
  std::map<TNode, TNode >::iterator itg;
  for( TNode a : assumptions )
  {
    itg = gassumptions.find(a);
    if(itg!=gassumptions.end() )
    {
      Trace("ied-conflict") << "INST-explain assumption: " << a << std::endl;
      Trace("ied-conflict") << "INST-explain from:       " << itg->second << std::endl;
    }
  }
  
  Trace("ied-conflict") << "Result of inst explain : " << std::endl;
  for (const std::pair<Node, bool>& ep : expresAtom)
  {
    rexp.push_back(ep.first);
    Trace("ied-conflict") << "* " << ep.first << std::endl;
  }
*/
  // TEMPORARY FIXME
  if (d_doExit)
  {
    exit(1);
  }
  return ret;
}

void InstExplainDb::instLitExplain(Node lit,
                                   std::map<Node, bool>& expres,
                                   std::map<Node, bool>& expresAtom,
                                   bool regressInst)
{
  /*
  if (regressInst)
  {
    Trace("ied-conflict-debug") << "--- " << lit;
    std::map<Node, InstExplainLit>::iterator itl = d_lit_explains.find(lit);
    if (itl != d_lit_explains.end())
    {
      // activate the literal
      activateLit(lit);
      Trace("ied-conflict-debug") << " inst-explanable ";
      std::vector<Node>& cexp = itl->second.d_curr_prop_exps;
      if (!cexp.empty())
      {
        Trace("ied-conflict-debug") << " by " << cexp[0] << std::endl;
        // Since it's not necessary a literal, go to explain
        instExplain(cexp[0], expres, expresAtom, regressInst);
        return;
      }
    }
    else
    {
      Trace("ied-conflict-debug") << " NOT inst-explanable" << std::endl;
    }
  }
  // Cannot explain it via instantiations, add it now
  // Notice that all literals at this point should be SAT literals, hence
  // we do not need to regress them from the theory here.
  expresAtom[lit] = true;
  */
}

void InstExplainDb::instExplain(Node n,
                                std::map<Node, bool>& expres,
                                std::map<Node, bool>& expresAtom,
                                bool regressInst)
{
  std::vector< Node > lits;
  instBoolExplain(n,expres,lits);
  for( const Node& lit : lits )
  {
    instLitExplain(lit,expres,expresAtom,regressInst);
  }
}
bool InstExplainDb::instBoolExplain(Node n,
                  std::map<Node, bool>& expres,
                  std::vector< Node >& lits)
{
 if (expres.find(n) != expres.end())
  {
    return true;
  }
  expres[n] = true;
  Assert(d_ev.evaluate(n) == 1);
  // must justify why n is true
  TNode atom = n.getKind() == NOT ? n[0] : n;
  bool pol = n.getKind() != NOT;
  Kind k = n.getKind();
  if (k == AND || k == OR)
  {
    if ((k == AND) == pol)
    {
      for (const Node& nc : atom)
      {
        Node ncp = pol ? nc : nc.negate();
        if( !instBoolExplain(ncp, expres, lits) )
        {
          return false;
        }
      }
    }
    // choose one that evaluates to true
    for (const Node& nc : atom)
    {
      if (d_ev.evaluate(nc) == (pol ? 1 : -1))
      {
        Node ncp = pol ? nc : nc.negate();
        instBoolExplain(ncp, expres, lits);
        return true;
      }
    }
    AlwaysAssert(false);
    return false;
  }
  else if (k == ITE)
  {
    int cbres = d_ev.evaluate(atom[0]);
    if (cbres == 0)
    {
      // branch is unknown, must do both
      if( !instBoolExplain(atom[1], expres, lits) || !instBoolExplain(atom[2], expres, lits) )
      {
        return false;
      }
    }
    else
    {
      // branch is known, do relevant child
      unsigned checkIndex = cbres > 0 ? 1 : 2;
      if( !instBoolExplain(atom[0], expres, lits) || !instBoolExplain(atom[checkIndex], expres, lits) )
      {
        return false;
      }
    }
  }
  else if (k == EQUAL && n[0].getType().isBoolean())
  {
    // must always do both
    if( !instBoolExplain(atom[0], expres, lits) || !instBoolExplain(atom[1], expres, lits) )
    {
      return false;
    }
  }
  else
  {
    lits.push_back(n);
  }
  return true;
}

void InstExplainDb::indent(const char* c, unsigned tb)
{
  for (unsigned i = 0; i < tb; i++)
  {
    Trace(c) << " ";
  }
}

bool InstExplainDb::regressExplain(EqExplainer* eqe, std::vector< TNode >& assumptions, eq::EqProof * eqp)
{
  if( eqp->d_id==eq::MERGED_THROUGH_EQUALITY )
  {
    // use the explainer
    if (eqe)
    {
      Assert( !eqp->d_node.isNull() );
      Trace("ied-conflict-debug") << "Explain: " << eqp->d_node << std::endl;
      return eqe->explain(eqp->d_node, assumptions, eqp);
    }
    return false;
  }
  for( unsigned i=0, nchild = eqp->d_children.size(); i<nchild; i++ )
  {
    if( !regressExplain(eqe,assumptions, eqp->d_children[i].get()) )
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
    d_doExit = true;
    Node cnode = eqp->d_node;
    Trace("ied-gen") << "ied-pf: congruence " << cnode << std::endl;
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
        unsigned ii = nchild-(i+1);
        retc =
            generalize(childProofs[ii], concs, concsg, tb + 1);
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
    Assert( ret==Rewriter::rewrite(ret) );
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
          Trace("ied-gen") << "ied-pf: inst-explain equality " << olit << " (from "
                          << pinst << ")" << std::endl;
          indent("ied-gen", tb + 1);
        }
        // we must inst-explain it now
        if( !runInstExplain(gli, ret, pinst, tb+2) )
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
    // we do not care about generalizations here
  }
  else if (id == eq::MERGED_THROUGH_CONSTANTS)
  {
    //???
    AlwaysAssert(false);
  }
  else if (id == eq::MERGED_THROUGH_TRANS)
  {
    d_doExit = true;
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
      Trace("ied-gen") << ", with " << itg->second.size() << " generalizations";
    }
    Trace("ied-gen") << std::endl;
  }
  return ret;
}

bool InstExplainDb::runInstExplain(GLitInfo& g, Node lit, Node inst, unsigned tb)
{
  InstExplainInst& iei = getInstExplainInst(inst);
  // Since the instantiation lemma inst is propagating lit, we have that:
  //   inst { lit -> false }
  // must evaluate to false in the current context.
  Node instExp = iei.getExplanationFor(lit);
  
  std::vector< Node > plits;
  // Second, get the SAT literals from inst that are propagating lit.
  // These literals are such that the propositional entailment holds:
  //   inst ^ plits[0] ^ ... ^ plits[k] |= lit
  std::map<Node, bool> cache;
  if( !instBoolExplain(instExp,cache,plits) )
  {
    Assert( false );
    return false;
  }

  // For each literal in plits, we must either regress it further, or add it to
  // the assumptions of g.
  for( const Node& pl : plits )
  {
    Assert( pl==Rewriter::rewrite(pl));
    // maybe it is inst-explainable
    std::map<Node, InstExplainLit>::iterator itl = d_lit_explains.find(pl);
    if (itl != d_lit_explains.end())
    {
      InstExplainLit& iel = itl->second;
      // activate the literal
      activateLit(pl);
      std::vector<Node>& cexp = iel.d_curr_insts;
      for (const Node& pinstc : cexp)
      {
        Node olit = iel.getOriginalLit(pinstc);
        // check if this is compatible 
        
        //GLitInfo gc;
        
      }
    }
    else
    {
      g.d_assumptions.push_back(pl);
      // we must drop this literal from g TODO
      
    }
  }
  // FIXME
  return false;
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
  Assert( n.getKind()==EQUAL );
  if( n[1]==d_true )
  {
    return n[0];
  }
  else if( n[1]==d_false )
  {
    n[0].negate();
  }
  return n;
}

bool InstExplainDb::isGeneralization(Node n, Node gn )
{
  // TODO
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
