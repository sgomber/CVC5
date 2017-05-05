/*********************                                                        */
/*! \file datatypes_sygus.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus utilities for theory of datatypes
 **
 ** Implementation of sygus utilities for theory of datatypes
 **/


#include "expr/node_manager.h"
#include "options/quantifiers_options.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/datatypes/datatypes_sygus_new.h"
#include "theory/quantifiers/term_database.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;

void SygusSplitNew::getSygusSplits( Node n, const Datatype& dt, std::vector< Node >& splits, std::vector< Node >& lemmas ) {
  Assert( dt.isSygus() );
  if( d_splits.find( n )==d_splits.end() ){
    Trace("sygus-split") << "Get sygus splits " << n << std::endl;
    //get the kinds for child datatype
    TypeNode tnn = n.getType();
    d_tds->registerSygusType( tnn );
    
    std::vector< Node > curr_splits;
    for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
      Trace("sygus-split-debug2") << "Add split " << n << " : constructor " << dt[i].getName() << " : ";
      if( !d_tds->isGenericRedundant( tnn, i ) ){
        std::vector< Node > test_c;
        test_c.push_back( DatatypesRewriter::mkTester( n, i, dt ) );
        //add fairness constraint
        if( options::ceGuidedInstFair()==quantifiers::CEGQI_FAIR_DT_SIZE ){
          Node szl = NodeManager::currentNM()->mkNode( DT_SIZE, n );
          Node szr = NodeManager::currentNM()->mkNode( DT_SIZE, DatatypesRewriter::getInstCons( n, dt, i ) );
          szr = Rewriter::rewrite( szr );
          test_c.push_back( szl.eqNode( szr ) );
        }
        Node test = test_c.size()==1 ? test_c[0] : NodeManager::currentNM()->mkNode( AND, test_c );
        curr_splits.push_back( test );
        Trace("sygus-split-debug2") << "SUCCESS" << std::endl;
        Trace("sygus-split-debug") << "Disjunct #" << curr_splits.size() << " : " << test << std::endl;
      }else{
        Trace("sygus-split-debug2") << "redundant operator" << std::endl;
      }
    }
    Assert( !curr_splits.empty() );
    Node split = curr_splits.size()==1 ? curr_splits[0] : NodeManager::currentNM()->mkNode( OR, curr_splits );
    d_splits[n].push_back( split );
  }
  //copy to splits
  splits.insert( splits.end(), d_splits[n].begin(), d_splits[n].end() );
}


SygusSymBreakNew::SygusSymBreakNew( quantifiers::TermDbSygus * tds, context::Context* c ) : d_tds( tds ), d_context( c ) {

}

SygusSymBreakNew::~SygusSymBreakNew() {

}

/** add tester */
void SygusSymBreakNew::addTester( int tindex, Node n, Node exp ) {
  
}

