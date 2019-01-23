/*********************                                                        */
/*! \file fp_ic_pass.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The ExtRewPre preprocessing pass
 **
 ** Applies the extended rewriter to assertions
 **/

#include "preprocessing/passes/fp_ic_pass.h"

#include "expr/node_algorithm.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {

FpIcPre::FpIcPre(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "fp-ic-pre"){};

int FpIcPre::getCtnIndex( Node x, Node n)
{
  int ctnIndex = -1;
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    if( expr::hasSubterm(n[i],x) ){
      if( ctnIndex==-1 ){
        ctnIndex = i;
      }else{
        return -1;
      }
    }
  }
  return ctnIndex;
}
Node FpIcPre::solve( Node x, Node p, std::vector< Node >& ics, int ctnIndex ){
  Trace("fp-ic-solve") << "Solve for " << x << " in " << p << ", ctnIndex=" << ctnIndex << std::endl;
  NodeManager * nm = NodeManager::currentNM();
  Kind pk = p.getKind();
  if( pk==NOT ){
    Kind pck = p[0].getKind();
    Kind fk = pck==FLOATINGPOINT_LEQ ? FLOATINGPOINT_GT : 
              ( pck==FLOATINGPOINT_GEQ ? FLOATINGPOINT_LT :
              ( pck==FLOATINGPOINT_GT ? FLOATINGPOINT_LEQ :
              ( pck==FLOATINGPOINT_LT ? FLOATINGPOINT_GEQ : UNDEFINED_KIND ) ) );
    if( fk==UNDEFINED_KIND ){
      Trace("fp-ic-solve") << " ....failed to handle negation." << std::endl;
      return Node::null();
    }else{
      Node pf = nm->mkNode( fk, p[0][0], p[0][1] );
      return solve(x,pf,ics,ctnIndex);
    }
  }
  if( ctnIndex==-1 ){
    ctnIndex = getCtnIndex(x,p);
    Trace("fp-ic-solve") << "...got ctnIndex " << ctnIndex << std::endl;
    if( ctnIndex==-1 ){
      Trace("fp-ic-solve") << " ....failed to find contains index." << std::endl;
      return Node::null();
    }
  }
  Node tx = p[ctnIndex];
  if( tx.getKind()==FLOATINGPOINT_NEG && pk==EQUAL ){
    Node eq = tx[0].eqNode(nm->mkNode(FLOATINGPOINT_NEG,p[1-ctnIndex]));
    return solve(x,eq,ics,0);
  }
  if( tx==x ){
    Node s = p[1-ctnIndex];
    if( pk==EQUAL || pk==FLOATINGPOINT_LEQ || pk==FLOATINGPOINT_GEQ ){
    Trace("fp-ic-solve") << "....success: " << s << std::endl;
      return s;
    }else{
      //Node k = nm->mkSkolem("k_strict", s.getType());
      //Trace("fp-ic-solve") << "....success: " << k << std::endl;
      Trace("fp-ic-solve") << " ....unknown predicate " << pk << std::endl;
      return Node::null();
    }
  }
  int tCtnIndex = getCtnIndex(x,tx);
  if( tCtnIndex==-1 ){
      Trace("fp-ic-solve") << " ....failed to find contains index in term." << std::endl;
    return Node::null();
  }
  Node k = nm->mkSkolem("k", tx[tCtnIndex].getType());
  Node eq = tx[tCtnIndex].eqNode(k);
  
  bool proc = false;
  Kind txk = tx.getKind();
  if( pk==EQUAL ){
    if( txk==FLOATINGPOINT_MULT ){
      proc = true;
    }else if( txk==FLOATINGPOINT_DIV && tCtnIndex==1 ){
      proc = true;
    }else if( txk==FLOATINGPOINT_PLUS ){
      proc = true;
    }
  }
  if( proc ){
    Trace("fp-ic-req") << "CHOICE: " << pk << "/" << txk << ", index : " << ctnIndex << "/" << tCtnIndex << std::endl;
  }else{
    Trace("fp-ic-req") << "REQUIRES: " << pk << "/" << txk << ", index : " << ctnIndex << "/" << tCtnIndex << std::endl;
  }
  return solve(x,eq,ics,0);
}
    
PreprocessingPassResult FpIcPre::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::vector< Node > quants;
  TNode cur;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node n = (*assertionsToPreprocess)[i];
    
    // search for quantifiers
    visit.push_back(n);
    do {
      cur = visit.back();
      visit.pop_back();
      if (visited.find(cur) == visited.end()) {
        visited.insert(cur);
        if( cur.getKind()==FORALL ){
          quants.push_back(cur);
        }
        for (const Node& cn : cur ){
          visit.push_back(cn);
        }
      }
    } while (!visit.empty());
  }
  
  for( const Node& q : quants )
  {
    Trace("fp-ic") << "FP-IC: Quantified formula : " << q << std::endl;
    std::vector< Node > qlits;
    if( q[1].getKind()==OR ){
      for( const Node& ql : q[1] ){
        qlits.push_back(ql.negate());
      }
    }else{
      qlits.push_back(q[1].negate());
    }
    std::vector< Node > ics;
    for( const Node& ql : qlits ){
      Trace("fp-ic") << "- literal to solve: " << ql << std::endl;
      for( unsigned j=0; j<q[0].getNumChildren(); j++ ){
        Node res = solve( q[0][j], ql, ics );
        if( !res.isNull() ){
        }
      }
    }
  }
  
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
