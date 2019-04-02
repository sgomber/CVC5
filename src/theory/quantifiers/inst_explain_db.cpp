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
                            std::vector<TNode>& assumptions)
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
      ee->explainEquality(atom[0], atom[1], pol, assumptions);
      Trace("eq-explain") << "finished explain eq " << assumptions.size()
                          << std::endl;
      return true;
    }
  }
  else if (ee->hasTerm(atom))
  {
    Trace("eq-explain") << "explain pred" << atom << " " << pol << std::endl;
    ee->explainPredicate(atom, pol, assumptions);
    Trace("eq-explain") << "finished explain pred " << assumptions.size()
                        << std::endl;
    return true;
  }
  return false;
}

bool EqExplainerEe::explain(Node lit, std::vector<TNode>& assumptions)
{
  return explainEe(d_ee, lit, assumptions);
}

bool EqExplainerTe::explain(Node lit, std::vector<TNode>& assumptions)
{
  // currently we use a very simple heuristic here: we try to explain
  // using UF's equality engine only.
  Theory* t = d_te->theoryOf(THEORY_UF);
  eq::EqualityEngine* ee = t->getEqualityEngine();
  if (ee)
  {
    return explainEe(ee, lit, assumptions);
  }
  return false;
}

InstExplainDb::InstExplainDb(QuantifiersEngine* qe)
    : d_qe(qe), d_ev(d_qe->getValuation())
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

void InstExplainDb::registerExplanation(Node inst, Node n, Node on)
{
  Trace("inst-explain") << "Get literals that are explanable by " << inst
                        << std::endl;
  std::map<bool, std::unordered_set<Node, NodeHashFunction> > visited;
  std::vector<bool> visit_hasPol;
  std::vector<Node> visit;
  std::vector<Node> visiti;
  bool hasPol;
  TNode cur;
  TNode curi;
  visit_hasPol.push_back(true);
  visit.push_back(on);
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
  if (iti == d_inst_explains.end())
  {
    InstExplainInst& iei = d_inst_explains[inst];
    iei.initialize(inst);
    return iei;
  }
  return iti->second;
}

ExplainStatus InstExplainDb::explain(const std::vector<Node>& exp,
                                     EqExplainer* eqe,
                                     std::vector<Node>& rexp,
                                     bool regressInst,
                                     const char* ctx)
{
  ExplainStatus ret = EXP_STATUS_FULL;
  std::map<Node, bool> proc_pre;
  std::map<Node, bool> proc;
  std::map<Node, bool> expres;
  std::map<Node, bool> expresAtom;
  std::map<Node, bool> processList;
  Trace("ied-conflict") << "Conflict in context " << ctx << " : " << std::endl;
  for (const Node& e : exp)
  {
    Node er = Rewriter::rewrite(e);
    if (proc_pre.find(er) == proc_pre.end())
    {
      proc_pre[er] = true;
      Trace("ied-conflict") << "* " << er << std::endl;
      // first, regress the explanation using the eqe utility
      std::vector<TNode> assumptions;
      bool regressExp = false;
      if (eqe)
      {
        Trace("ied-conflict-debug") << "Explain: " << er << std::endl;
        if (eqe->explain(er, assumptions))
        {
          regressExp = true;
          Trace("ied-conflict-debug")
              << "  ...regressed to " << assumptions << std::endl;
        }
        else
        {
          Trace("ied-conflict-debug") << "  ...failed to regress" << std::endl;
        }
      }
      if (!regressExp)
      {
        assumptions.push_back(er);
        // if we did not explain it, then we need to set the status
        // however, we could still hope that this assertion simply holds in the
        // current context
        ret = EXP_STATUS_INCOMPLETE;
      }
      for (TNode ert : assumptions)
      {
        // now, regress the equality in terms of instantiation lemmas
        Assert(Rewriter::rewrite(ert) == ert);
        if (proc.find(ert) != proc.end())
        {
          continue;
        }
        proc[ert] = true;
        Trace("ied-conflict-debug") << "*** " << ert << std::endl;
        if (regressInst)
        {
          instExplain(ert, expres, expresAtom, processList, regressInst);
        }
        else
        {
          expresAtom[ert] = true;
        }
      }
    }
  }
  // Now, go back and process atoms that are explainable in multiple ways.
  // This is an optimization for constructing smaller explanations.
  while (!processList.empty())
  {
    std::map<Node, bool> newProcessList;
    std::map<Node, std::vector<Node> > expToLit;
    for (const std::pair<Node, bool>& p : processList)
    {
      Node ert = p.first;
      InstExplainLit& ie = getInstExplainLit(ert);
      std::vector<Node>& cexp = ie.d_curr_prop_exps;
      // first check if this literal is already explained, if so, drop it.
      bool alreadyProc = false;
      for (const Node& iexp : cexp)
      {
        if (expres.find(iexp) != expres.end())
        {
          alreadyProc = true;
          break;
        }
      }
      if (!alreadyProc)
      {
        // If not already explained, add this literal to the list of literals
        // for each of its explanation. We choose the best explanation below.
        for (const Node& iexp : cexp)
        {
          expToLit[iexp].push_back(ert);
        }
        newProcessList[ert] = true;
      }
    }
    if (!expToLit.empty())
    {
      // Must decide to explain one literal. We choose the instantiation
      // explanation that covers the maximum number of literals in the process
      // list.
      unsigned max = 0;
      Node maxExp;
      for (const std::pair<Node, std::vector<Node> >& e : expToLit)
      {
        if (e.second.size() > max)
        {
          maxExp = e.first;
          max = e.second.size();
        }
      }
      Assert(!maxExp.isNull());
      instExplain(maxExp, expres, expresAtom, newProcessList, regressInst);
      Trace("ied-conflict-debug")
          << "--- add inst-explain " << maxExp << " covering " << max
          << " literals" << std::endl;
      Assert(!expToLit[maxExp].empty());
      // update the process list to remove the literals
      for (const Node& lit : expToLit[maxExp])
      {
        Assert(newProcessList.find(lit) != newProcessList.end());
        newProcessList.erase(lit);
      }
    }
    processList = newProcessList;
  }
  Trace("ied-conflict") << "Result of inst explain : " << std::endl;
  for (const std::pair<Node, bool>& ep : expresAtom)
  {
    rexp.push_back(ep.first);
    Trace("ied-conflict") << "* " << ep.first << std::endl;
  }
  return ret;
}

void InstExplainDb::instLitExplain(Node lit,
                                   std::map<Node, bool>& expres,
                                   std::map<Node, bool>& expresAtom,
                                   std::map<Node, bool>& processList,
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
      if (cexp.size() == 1)
      {
        Trace("ied-conflict-debug") << " by " << cexp[0] << std::endl;
        // Since it's not necessary a literal, go to explain
        instExplain(cexp[0], expres, expresAtom, processList, regressInst);
        return;
      }
      else
      {
        Trace("ied-conflict-debug")
            << " in " << cexp.size() << "/" << itl->second.d_insts.size()
            << " ways" << std::endl;
        if (!cexp.empty())
        {
          // otherwise we have a choice, add to process list
          processList[lit] = true;
          return;
        }
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
                                std::map<Node, bool>& processList,
                                bool regressInst)
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
        instExplain(ncp, expres, expresAtom, processList, regressInst);
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
          instExplain(ncp, expres, expresAtom, processList, regressInst);
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
      instExplain(atom[1], expres, expresAtom, processList, regressInst);
      instExplain(atom[2], expres, expresAtom, processList, regressInst);
    }
    else
    {
      // branch is known, do relevant child
      unsigned checkIndex = cbres > 0 ? 1 : 2;
      instExplain(atom[0], expres, expresAtom, processList, regressInst);
      instExplain(
          atom[checkIndex], expres, expresAtom, processList, regressInst);
    }
  }
  else if (k == EQUAL && n[0].getType().isBoolean())
  {
    // must always do both
    instExplain(atom[0], expres, expresAtom, processList, regressInst);
    instExplain(atom[1], expres, expresAtom, processList, regressInst);
  }
  else
  {
    instLitExplain(n, expres, expresAtom, processList, regressInst);
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
