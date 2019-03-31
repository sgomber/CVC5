/*********************                                                        */
/*! \file inst_explain.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of instantiate
 **/

#include "theory/quantifiers/inst_explain.h"

#include "options/quantifiers_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void InstExplainLit::initialize(Node inst)
{
  d_this = inst;
}
  
void InstExplainLit::addInstExplanation(Node inst)
{
  if (std::find(d_insts.begin(), d_insts.end(), inst) == d_insts.end())
  {
    d_insts.push_back(inst);
    // TODO: store the explanation
    
  }
}

void InstExplainInst::initialize(Node inst)
{
  d_this = inst;
}

void InstExplainInst::propagate( InstExplainDb& ied, QuantifiersEngine * qe )
{
  // if possible, propagate the literal in the clause that must be true
  
  
}

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
      Trace("eq-explain") << "finished explain eq " << assumptions.size() << std::endl;
      return true;
    }
  }
  else if (ee->hasTerm(atom))
  {
    Trace("eq-explain") << "explain pred" << atom << " " << pol << std::endl;
    ee->explainPredicate(atom, pol, assumptions);
    Trace("eq-explain") << "finished explain pred " << assumptions.size() << std::endl;
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

InstExplainDb::InstExplainDb(QuantifiersEngine * qe) : d_qe(qe)
{
  d_false = NodeManager::currentNM()->mkConst(false);
  d_true = NodeManager::currentNM()->mkConst(true);
}

void InstExplainDb::reset(Theory::Effort e)
{
  d_active_lexp.clear();
  d_active_inst.clear();
}
void InstExplainDb::activateLit(Node lit)
{
  if( d_active_lexp.find(lit)==d_active_lexp.end() )
  {
    d_active_lexp[lit] = true;
    std::map< Node, InstExplainLit >::iterator itl = d_lit_explains.find(lit);
    Assert( itl!=d_lit_explains.end() );
    // propagate for all insts
    for( const Node& i : itl->second.d_insts )
    {
      activateInst(i);
    }
  }
}

void InstExplainDb::activateInst(Node inst)
{
  if( d_active_inst.find(inst)==d_active_inst.end() )
  {
    d_active_inst[inst] = true;
    
    // TODO
  }
}

void InstExplainDb::registerExplanation(Node inst, Node n)
{
  Trace("inst-explain") << "Get literals that are explanable by " << inst
                        << std::endl;
  inst = TermUtil::simpleNegate(inst);
  std::map<bool, std::unordered_set<TNode, TNodeHashFunction> > visited;
  std::vector<bool> visit_hasPol;
  std::vector<TNode> visit;
  bool hasPol;
  TNode cur;
  visit_hasPol.push_back(true);
  visit.push_back(n);
  TNode ft = d_false;
  TNode tt = d_true;
  do
  {
    hasPol = visit_hasPol.back();
    cur = visit.back();
    visit.pop_back();
    if (visited[hasPol].find(cur) == visited[hasPol].end())
    {
      visited[hasPol].insert(cur);

      TNode atom = cur.getKind() == NOT ? cur[0] : cur;
      bool pol = cur.getKind() != NOT;
      Kind k = atom.getKind();
      if (k == AND || k == OR)
      {
        for (const Node& ac : atom)
        {
          Node acp = pol ? ac : ac.negate();
          visit_hasPol.push_back(hasPol);
          visit.push_back(acp);
        }
      }
      else if (k == ITE)
      {
        for (unsigned i = 0; i < 2; i++)
        {
          Node ac = atom[i + 1];
          Node acp = pol ? ac : ac.negate();
          visit_hasPol.push_back(hasPol);
          visit.push_back(acp);
        }
        visit_hasPol.push_back(false);
        visit.push_back(atom[0]);
      }
      else if (k == EQUAL && atom[0].getType().isBoolean())
      {
        for (unsigned i = 0; i < 2; i++)
        {
          visit_hasPol.push_back(false);
          visit.push_back(atom[i]);
        }
      }
      else
      {
        InstExplainLit& iel = getInstExplainLit(cur);
        iel.addInstExplanation(inst);
        Trace("inst-explain") << "  -> " << cur << std::endl;
        if (!hasPol)
        {
          Node curn = cur.negate();
          InstExplainLit& ieln = getInstExplainLit(curn);
          ieln.addInstExplanation(inst);
          Trace("inst-explain") << "  -> " << curn << std::endl;
        }
      }
    }
  } while (!visit.empty());
}

InstExplainLit& InstExplainDb::getInstExplainLit(Node lit)
{
  std::map<Node, InstExplainLit>::iterator itl = d_lit_explains.find(lit);
  if( itl==d_lit_explains.end() )
  {
    d_lit_explains[lit].initialize(lit);
    return d_lit_explains[lit];
  }
  return itl->second;
}

ExplainStatus InstExplainDb::explain(const std::vector<Node>& exp,
                            EqExplainer* eqe,
                            std::vector<Node>& rexp,
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
          Trace("ied-conflict-debug")
              << "  ...failed to regress" << std::endl;
        }
      }
      if (!regressExp)
      {
        assumptions.push_back(er);
        // if we did not explain it, then we need to set the status
        // however, we could still hope that this assertion simply holds in the
        // current context.
        
        ret = EXP_STATUS_INCOMPLETE;
      }
      for (TNode ert : assumptions)
      {
        // now, regress the equality in terms of instantiation lemmas
        Assert(Rewriter::rewrite(ert) == ert);
        if (proc.find(ert) == proc.end())
        {
          proc[ert] = true;
          Trace("ied-conflict-debug") << "*** " << ert << std::endl;
#if 1
          insertExpResult(ert, expres, expresAtom); 
#else     
          TNode ft = d_false;
          std::map<Node, InstExplain>::iterator itle = d_lit_explains.find(ert);
          bool explained = false;
          if( itle!=d_lit_explains.end() )
          {
            activateLit(ert);
            std::vector< Node >& iei = itle->second.d_active_insts;
            if (iei.size() == 1)
            {
              Trace("ied-conflict-debug")
                  << "    inst-explanable by " << iei[0] << std::endl;
              insertExpResult(iei[0], expres, expresAtom);
              explained = true;
            }
            else if( !iei.empty() )
            {
              Trace("ied-conflict-debug")
                  << "    inst-explanable in " << iei.size() << " ways"
                  << std::endl;
              // otherwise we have a choice
              processList[ert] = true;
              explained = true;
            }
          }
          if( !explained )
          {
            Trace("ied-conflict-debug")
                << "    NOT inst-explanable" << std::endl;
            insertExpResult(ert, expres, expresAtom);   
          }
#endif
        }
      }
    }
  }
#if 0
  // now, go back and process atoms that are explainable in multiple ways
  // this is an optimization for constructing smaller explanations
  while (!processList.empty())
  {
    std::map<Node, bool> newProcessList;
    std::map<Node, std::vector<Node> > expToLit;
    for (const std::pair<Node, bool>& p : processList)
    {
      Node ert = p.first;
      InstExplainLit& ie = getInstExplainLit(ert);
      std::vector< Node >& iei = ie.d_active_insts;
      bool alreadyProc = false;
      for (const Node& iexp : iei)
      {
        if (expres.find(iexp) != expres.end())
        {
          alreadyProc = true;
          break;
        }
      }
      if (!alreadyProc)
      {
        for (const Node& iexp : iei)
        {
          expToLit[iexp].push_back(ert);
        }
        newProcessList[ert] = true;
      }
    }
    if (!expToLit.empty())
    {
      // must decide to add one (choose max)
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
      insertExpResult(maxExp, expres, expresAtom);
      Trace("ied-conflict-debug")
          << "Add inst-explain " << maxExp << " covering " << max << " literals"
          << std::endl;
      Assert(!expToLit[maxExp].empty());
      for (const Node& lit : expToLit[maxExp])
      {
        Assert(newProcessList.find(lit) != newProcessList.end());
        newProcessList.erase(lit);
      }
    }
    processList = newProcessList;
  }
#endif
  Trace("ied-conflict") << "Result of inst explain : " << std::endl;
  for (const std::pair<Node, bool>& ep : expresAtom)
  {
    rexp.push_back(ep.first);
    Trace("ied-conflict") << "* " << ep.first << std::endl;
  }
  return ret;
}
void InstExplainDb::insertExpResult(Node exp,
                                    std::map<Node, bool>& expres,
                                    std::map<Node, bool>& expresAtom)
{
  expres[exp] = true;
  if (exp.getKind() == AND)
  {
    for (const Node& e : exp)
    {
      expresAtom[e] = true;
    }
  }
  else
  {
    expresAtom[exp] = true;
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
