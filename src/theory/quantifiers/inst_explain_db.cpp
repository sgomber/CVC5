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

bool EqExplainer::explainEe(eq::EqualityEngine* ee,
                            Node lit,
                            std::vector<TNode>& assumptions,
                            eq::EqProof* eqp)
{
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool pol = lit.getKind() != NOT;
  if (atom.getKind() == EQUAL)
  {
    if (ee->hasTerm(atom[0]) && ee->hasTerm(atom[1]))
    {
      if (pol)
      {
        if (!ee->areEqual(atom[0], atom[1]))
        {
          return false;
        }
      }
      else if (!ee->areDisequal(atom[0], atom[1], true))
      {
        return false;
      }
      Trace("eq-explain") << "explain eq" << atom << " " << pol << std::endl;
      ee->explainEquality(atom[0], atom[1], pol, assumptions, eqp);
      Trace("eq-explain") << "finished explain eq " << assumptions.size()
                          << std::endl;
      return true;
    }
  }
  else if (ee->hasTerm(atom))
  {
    Trace("eq-explain") << "explain pred" << atom << " " << pol << std::endl;
    ee->explainPredicate(atom, pol, assumptions, eqp);
    Trace("eq-explain") << "finished explain pred " << assumptions.size()
                        << std::endl;
    return true;
  }
  return false;
}

bool EqExplainerEe::explain(Node lit,
                            std::vector<TNode>& assumptions,
                            eq::EqProof* eqp)
{
  return explainEe(d_ee, lit, assumptions, eqp);
}

bool EqExplainerTe::explain(Node lit,
                            std::vector<TNode>& assumptions,
                            eq::EqProof* eqp)
{
  // currently we use a very simple heuristic here: we try to explain
  // using UF's equality engine only.
  Theory* t = d_te->theoryOf(THEORY_UF);
  eq::EqualityEngine* ee = t->getEqualityEngine();
  if (ee)
  {
    return explainEe(ee, lit, assumptions, eqp);
  }
  return false;
}

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
                                     const std::vector<Node>& exp,
                                     const std::vector<Node>& gexp,
                                     EqExplainer* eqe,
                                     std::vector<Node>& rexp,
                                     bool regressInst,
                                     const char* ctx)
{
  ExplainStatus ret = EXP_STATUS_FAIL;
  std::map<Node, bool> proc_pre;
  std::map<Node, bool> expres;
  std::map<Node, bool> expresAtom;
  if( Trace.isOn("ied-conflict") )
  {
    Trace("ied-conflict") << "Conflict in context " << ctx << " : " << std::endl;
    for (unsigned i = 0, esize = exp.size(); i < esize; i++)
    {
      Trace("ied-conflict") << "  [" << i << "] " << exp[i] << std::endl;
      Trace("ied-conflict") << "  GEN " << gexp[i] << std::endl;
    }
  }
  Assert(exp.size() == gexp.size());
  // the virtual instantiation lemma
  InstExplainInst conflict;
  conflict.initialize(q,Node::null(),terms);
  // the generalization information across all literals
  GLitInfo genInfo;
  genInfo.initialize(&conflict);
  std::vector<TNode> assumptions;
  // Possible generalized assumptions
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
          /*
          Debug("ied-proof") << "LFSC:" << std::endl;
          std::stringstream ss;
          ProofUF * pfu = new ProofUF(pf);
          pfu->toStream(ss);
          Debug("ied-proof") << ss.str();
          */
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
*/
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
void InstExplainDb::instBoolExplain(Node n,
                  std::map<Node, bool>& expres,
                  std::vector< Node >& lits)
{
 if (expres.find(n) != expres.end())
  {
    return;
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
        instBoolExplain(ncp, expres, lits);
      }
    }
    else
    {
      // choose one that evaluates to true
      for (const Node& nc : atom)
      {
        if (d_ev.evaluate(nc) == (pol ? 1 : -1))
        {
          Node ncp = pol ? nc : nc.negate();
          instBoolExplain(ncp, expres, lits);
          return;
        }
      }
      AlwaysAssert(false);
    }
  }
  else if (k == ITE)
  {
    int cbres = d_ev.evaluate(atom[0]);
    if (cbres == 0)
    {
      // branch is unknown, must do both
      instBoolExplain(atom[1], expres, lits);
      instBoolExplain(atom[2], expres, lits);
    }
    else
    {
      // branch is known, do relevant child
      unsigned checkIndex = cbres > 0 ? 1 : 2;
      instBoolExplain(atom[0], expres, lits);
      instBoolExplain(atom[checkIndex], expres, lits);
    }
  }
  else if (k == EQUAL && n[0].getType().isBoolean())
  {
    // must always do both
    instBoolExplain(atom[0], expres, lits);
    instBoolExplain(atom[1], expres, lits);
  }
  else
  {
    lits.push_back(n);
  }
}

void InstExplainDb::indent(const char* c, unsigned tb)
{
  for (unsigned i = 0; i < tb; i++)
  {
    Trace(c) << " ";
  }
}
Node InstExplainDb::generalize(
    Node e,
    Node ge,
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
    Assert(e.isNull());
    Assert(ge.isNull());
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
        // FIXME: must move up
        retc =
            generalize(d_null, d_null, childProofs[i], concs, concsg, tb + 1);
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
        gli.initialize(&getInstExplainInst(pinst));
        gli.d_reqInstExplains[ret] = pinst;
        if (Trace.isOn("ied-gen"))
        {
          indent("ied-gen", tb + 1);
          Trace("ied-gen") << "ied-pf: gen-equality " << olit << " (from "
                           << pinst << ")" << std::endl;
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
      // FIXME: must move up
      retc = generalize(d_null, d_null, epi, concs, concsg, tb + 1);
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
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
