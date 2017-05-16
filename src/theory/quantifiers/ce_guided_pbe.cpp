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

void CegConjecturePbe::collectExamples( Node n, std::map< Node, bool >& visited, bool hasPol, bool pol ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    Node neval;
    Node n_output;
    if( n.getKind()==APPLY_UF && n.getNumChildren()>0 ){
      neval = n;
      if( hasPol ){
        n_output = NodeManager::currentNM()->mkConst( !pol );
      }
    }else if( n.getKind()==EQUAL && hasPol && !pol ){
      for( unsigned r=0; r<2; r++ ){
        if( n[r].getKind()==APPLY_UF && n[r].getNumChildren()>0 ){
          neval = n[r];
          if( n[1-r].isConst() ){
            n_output = n[1-r];
          }
        }
      }
    }
    if( !neval.isNull() ){
      if( neval.getKind()==APPLY_UF && neval.getNumChildren()>0 ){
        // is it an evaluation function?
        std::map< Node, bool >::iterator itx = d_examples_invalid.find( neval[0] );
        if( itx!=d_examples_invalid.end() ){
          if( !itx->second ){
            //collect example
            bool success = true;
            std::vector< Node > ex;
            for( unsigned j=1; j<neval.getNumChildren(); j++ ){
              if( !neval[j].isConst() ){
                success = false;
                break;
              }else{
                ex.push_back( neval[j] );
              }
            }
            if( success ){
              d_examples[neval[0]].push_back( ex );
              d_examples_out[neval[0]].push_back( n_output );
              d_examples_term[neval[0]].push_back( neval );
              if( n_output.isNull() ){
                d_examples_out_invalid[neval[0]] = true;
              }else{
                Assert( n_output.isConst() );
              }
              //finished processing this node
              return;
            }else{
              d_examples_invalid[neval[0]] = true;
              d_examples_out_invalid[neval[0]] = true;
            }
          }
        }
      }
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      bool newHasPol;
      bool newPol;
      QuantPhaseReq::getPolarity( n, i, hasPol, pol, newHasPol, newPol );
      collectExamples( n[i], visited, newHasPol, newPol );
    }
  }
}

void CegConjecturePbe::initialize( Node q ) {
  Trace("sygus-pbe") << "Initialize PBE : " << q << std::endl;
  
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    d_examples[q[0][i]].clear();
    d_examples_invalid[q[0][i]] = false;
    d_examples_out[q[0][i]].clear();
    d_examples_out_invalid[q[0][i]] = false;
    d_examples_term[q[0][i]].clear();
  }
  
  std::map< Node, bool > visited;
  collectExamples( q[1], visited, true, true );
  
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
        if( !d_examples_out[v][j].isNull() ){
          Trace("sygus-pbe") << " -> " << d_examples_out[v][j];
        }
        Trace("sygus-pbe") << std::endl;
      }
    }
  }
}

bool CegConjecturePbe::getPbeExamples( TNode v, TNode e, std::vector< std::vector< Node > >& exs, 
                                       std::vector< Node >& exos, std::vector< Node >& exts ) {
  std::map< Node, bool >::iterator itx = d_examples_invalid.find( v );
  if( itx!=d_examples_invalid.end() ){
    if( !itx->second ){
      Assert( d_examples.find( v )!=d_examples.end() );
      exs = d_examples[v];
      Assert( d_examples_out.find( v )!=d_examples_out.end() );
      exos = d_examples_out[v];
      //exts = d_examples_term[v];
      std::map< Node, std::vector< Node > >::iterator itx = d_examples_term.find( v );
      Assert( itx!=d_examples_term.end() );
      for( unsigned i=0; i<itx->second.size(); i++ ){
        Node subs = itx->second[i].substitute( v, e );
        exts.push_back( subs );
      }      
      return true;
    }
  }
  return false;
}

}
