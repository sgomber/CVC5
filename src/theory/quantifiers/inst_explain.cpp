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

void InstExplainDb::explain( std::vector< Node >& exp )
{
  std::map< Node, bool > proc;
  Trace("qcf-conflict-exp") << "Explanation is: " << std::endl;
  for (const Node& e : exp)
  {
    Node er = Rewriter::rewrite(e);
    if( proc.find(er)==proc.end() )
    {
      proc[er] = true;
      Trace("qcf-conflict-exp") << "  " << er << std::endl;
      TNode ert = er;
      TNode ft = d_false;
      InstExplain& ie = getInstExplain(er);
      for( const Node& iexp : ie.d_insts )
      {
        Node iexps = iexp.substitute(ert,ft);
        iexps = Rewriter::rewrite(iexps);
        Trace("qcf-conflict-exp-debug") << "    inst-explanable by " << iexps << std::endl;
      }
    }
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
