/*********************                                                        */
/*! \file ce_guided_pbe.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing programming by examples synthesis conjectures
 **
 **/
#include "theory/quantifiers/ce_guided_pbe.h"

#include "expr/datatype.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/term_database.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

CegConjecturePbe::CegConjecturePbe(QuantifiersEngine* qe, CegConjecture* p)
    : d_qe(qe),
      d_parent(p){

}

CegConjecturePbe::~CegConjecturePbe() {

}

void CegConjecturePbe::collectExamples( Node n, std::map< Node, bool >& visited ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;  
    if( n.getKind()==APPLY_UF && n.getNumChildren()>0 ){
      // is it an evaluation function?
      std::map< Node, bool >::iterator itx = d_examples_invalid.find( n[0] );
      if( itx!=d_examples_invalid.end() ){
        if( !itx->second ){
          //collect example
          bool success = true;
          std::vector< Node > ex;
          for( unsigned j=1; j<n.getNumChildren(); j++ ){
            if( !n[j].isConst() ){
              success = false;
              break;
            }else{
              ex.push_back( n[j] );
            }
          }
          if( success ){
            d_examples[n[0]].push_back( ex );
          }else{
            d_examples_invalid[n[0]] = true;
          }
        }
      }
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      collectExamples( n[i], visited );
    }
  }
}

void CegConjecturePbe::initialize( Node q ) {
  Trace("sygus-pbe") << "Initialize PBE : " << q << std::endl;
  
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    d_examples_invalid[q[0][i]] = false;
  }
  
  std::map< Node, bool > visited;
  collectExamples( q[1], visited );
  
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    Node v = q[0][i];
    Trace("sygus-pbe") << "  examples for " << v << " : ";
    if( d_examples_invalid[v] ){
      Trace("sygus-pbe") << "INVALID" << std::endl;
    }else{
      Trace("sygus-pbe") << std::endl;
      for( unsigned j=0; j<d_examples[v].size(); j++ ){
        Trace("sygus-pbe") << "    ";
        for( unsigned k=0; k<d_examples[v][j].size(); k++ ){
          Trace("sygus-pbe") << d_examples[v][j][k] << " ";
        }
        Trace("sygus-pbe") << std::endl;
      }
    }
  }
}

bool CegConjecturePbe::getPbeExamples( Node v, std::vector< std::vector< Node > >& exs ) {
  std::map< Node, bool >::iterator itx = d_examples_invalid.find( v );
  if( itx!=d_examples_invalid.end() ){
    if( !itx->second ){
      exs = d_examples[v];
      return true;
    }
  }
  return false;
}

}
