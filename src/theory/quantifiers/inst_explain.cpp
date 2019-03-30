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
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool EqExplainer::explainEe(eq::EqualityEngine * ee, Node lit, std::vector<TNode>& assumptions)
{
  Node atom = lit.getKind()==NOT ? lit[0] : lit;
  bool pol = lit.getKind()!=NOT;
  
  if( atom.getKind()==EQUAL )
  {
    if( ee->hasTerm(atom[0]) && ee->hasTerm(atom[1]) )
    {
      if( pol )
      {
        if( !ee->areEqual(atom[0],atom[1]) )
        {
          return false;
        }
      }
      else if( !ee->areDisequal(atom[0],atom[1],true) )
      {
        return false;
      }
      ee->explainEquality(atom[0], atom[1], pol, assumptions);
      return true;
    }
  }
  else if( ee->hasTerm(atom) )
  {
    ee->explainPredicate(atom, pol, assumptions);
  }
  return false;
}

bool EqExplainerEe::explain(Node lit, std::vector<TNode>& assumptions)
{
  return explainEe(d_ee,lit,assumptions);
}
  
bool EqExplainerTe::explain(Node lit, std::vector<TNode>& assumptions)
{
  //FIXME
  //return explainEe(ee,lit,assumptions);
  return false;
}

InstExplainDb::InstExplainDb()
{
  d_false = NodeManager::currentNM()->mkConst(false);
}

void InstExplainDb::registerExplanation(Node inst, Node n)
{
  Trace("inst-explain") << "Get literals that are explanable by " << inst << std::endl;
  std::map< bool, std::unordered_set<TNode, TNodeHashFunction> > visited;
  std::vector<bool> visit_hasPol;
  std::vector<TNode> visit;
  bool hasPol;
  TNode cur;
  visit_hasPol.push_back(true);
  visit.push_back(n);
  do {
    hasPol = visit_hasPol.back();
    cur = visit.back();
    visit.pop_back();
    if (visited[hasPol].find(cur) == visited[hasPol].end()) {
      visited[hasPol].insert(cur);
      
      TNode atom = cur.getKind()==NOT ? cur[0] : cur;
      bool pol = cur.getKind()!=NOT;
      Kind k = atom.getKind();
      if( k==AND || k==OR )
      {
        for( const Node& ac : atom )
        {
          Node acp = pol ? ac : ac.negate();
          visit_hasPol.push_back(hasPol);
          visit.push_back(acp);
        }
      }
      else if( k==ITE )
      {
        for( unsigned i=0; i<2; i++ )
        {
          Node ac = atom[i+1];
          Node acp = pol ? ac : ac.negate();
          visit_hasPol.push_back(hasPol);
          visit.push_back(acp);
        }
        visit_hasPol.push_back(false);
        visit.push_back(atom[0]);
      }
      else if( k==EQUAL && atom[0].getType().isBoolean() )
      {
        for( unsigned i=0; i<2; i++ )
        {
          visit_hasPol.push_back(false);
          visit.push_back(atom[i]);
        }
      }
      else
      {
        d_lit_explains[cur].d_insts.push_back(inst);
        Trace("inst-explain") << "  -> " << cur << std::endl;
        if( !hasPol )
        {
          Node curn = cur.negate();
          d_lit_explains[curn].d_insts.push_back(inst);
        Trace("inst-explain") << "  -> " << curn << std::endl;
        }
      }
    }
  }while (!visit.empty());
}


InstExplain& InstExplainDb::getInstExplain( Node lit )
{ 
  return d_lit_explains[lit]; 
}

void InstExplainDb::explain( std::vector< Node >& exp, EqExplainer * eqe, const char * ctx )
{
  std::map< Node, bool > proc;
  Trace("ied-conflict") << "Conflict in context " << ctx << " : " << std::endl;
  for (const Node& e : exp)
  {
    Node er = Rewriter::rewrite(e);
    if( proc.find(er)==proc.end() )
    {
      proc[er] = true;
      Trace("ied-conflict") << "* " << er << std::endl;
      std::vector< TNode > assumptions;
      bool regressExp = false;
      if( eqe )
      {
        if( eqe->explain(er,assumptions) )
        {
          regressExp = true;
          Trace("ied-conflict") << "  ...regressed to " << assumptions << std::endl;
        }
      }
      if( !regressExp )
      {
        assumptions.push_back(er);
      }
      for( TNode ert : assumptions )
      {
        if( proc.find(ert)==proc.end() )
        {
          proc[ert] = true;
          Trace("ied-conflict") << "*** " << ert << std::endl;
          TNode ft = d_false;
          InstExplain& ie = getInstExplain(er);
          for( const Node& iexp : ie.d_insts )
          {
            Node iexps = iexp.substitute(ert,ft);
            iexps = Rewriter::rewrite(iexps);
            Trace("ied-conflict") << "    inst-explanable by " << iexps << std::endl;
          }
        }
      }
    }
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
