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
  d_tds = d_qe->getTermDatabaseSygus();
}

CegConjecturePbe::~CegConjecturePbe() {

}

//--------------------------------- collecting finite input/output domain information

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
        if( d_examples.find( neval[0] )!=d_examples.end() ){
          std::map< Node, bool >::iterator itx = d_examples_invalid.find( neval[0] );
          if( itx==d_examples_invalid.end() ){
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

void CegConjecturePbe::initialize( Node n, std::vector< Node >& candidates ) {
  Trace("sygus-pbe") << "Initialize PBE : " << n << std::endl;
  
  for( unsigned i=0; i<candidates.size(); i++ ){
    Node v = candidates[i];
    d_examples[v].clear();
    d_examples_out[v].clear();
    d_examples_term[v].clear();
  }
  
  std::map< Node, bool > visited;
  collectExamples( n, visited, true, true );
  
  for( unsigned i=0; i<candidates.size(); i++ ){
    Node v = candidates[i];
    Trace("sygus-pbe") << "  examples for " << v << " : ";
    if( d_examples_invalid.find( v )!=d_examples_invalid.end() ){
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

bool CegConjecturePbe::getPbeExamples( Node v, std::vector< std::vector< Node > >& exs, 
                                       std::vector< Node >& exos, std::vector< Node >& exts ) {
  std::map< Node, bool >::iterator itx = d_examples_invalid.find( v );
  if( itx==d_examples_invalid.end() ){
    Assert( d_examples.find( v )!=d_examples.end() );
    exs = d_examples[v];
    Assert( d_examples_out.find( v )!=d_examples_out.end() );
    exos = d_examples_out[v];
    Assert( d_examples_term.find( v )!=d_examples_term.end() );
    exts = d_examples_term[v];
    return true;
  }
  return false;
}


// ----------------------------- establishing enumeration types

void CegConjecturePbe::registerCandidates( std::vector< Node >& candidates ) {
  if( candidates.size()==1 ){  // conditional solutions for multiple function conjectures TODO?
    // collect a pool of types over which we will enumerate terms 
    Node e = candidates[0];
    collectEnumeratorTypes( e, e.getType() );
    // now construct the enumerators
    for( std::map< TypeNode, EnumTypeInfo >::iterator iti = d_tinfo.begin(); iti != d_tinfo.end(); ++iti ){
      TypeNode tn = iti->first;
      // register type
      Node ee = NodeManager::currentNM()->mkSkolem( "ee", tn );
      registerEnumerator( ee, e, tn, -1 );
      Trace("sygus-unif-debug") << "...enumerate " << ee << " for " << ((DatatypeType)tn.toType()).getDatatype().getName() << std::endl;
      for( unsigned j=0; j<iti->second.d_csol_cts.size(); j++ ){
        if( iti->second.d_template.find( j )!=iti->second.d_template.end() ){
          // it is templated, allocate a fresh variable
          Node et = NodeManager::currentNM()->mkSkolem( "et", iti->second.d_csol_cts[j] );
          Trace("sygus-unif-debug") << "...enumerate " << et << " of type " << ((DatatypeType)iti->second.d_csol_cts[j].toType()).getDatatype().getName();
          Trace("sygus-unif-debug") << " for arg " << j << " of " << ((DatatypeType)tn.toType()).getDatatype().getName() << std::endl;
          registerEnumerator( et, e, tn, j );
        }
      }
    }
  }
}

void CegConjecturePbe::registerEnumerator( Node et, Node e, TypeNode tn, int j ) {
  //d_qe->getTermDatabaseSygus()->registerMeasuredTerm( et, e );
  d_tinfo[tn].d_esyms[j] = et;
  d_einfo[et].d_parent_candidate = e;
  d_einfo[et].d_parent = tn;
  if( j>=0 ){
    d_einfo[et].d_arg = j;
  }
  d_esym_list[e].push_back( et );
  // make the guard
  Node eg = Rewriter::rewrite( NodeManager::currentNM()->mkSkolem( "eG", NodeManager::currentNM()->booleanType() ) );
  eg = d_qe->getValuation().ensureLiteral( eg );
  AlwaysAssert( !eg.isNull() );
  d_qe->getOutputChannel().requirePhase( eg, true );
  //add immediate lemma
  Node lem = NodeManager::currentNM()->mkNode( OR, eg, eg.negate() );
  Trace("cegqi-lemma") << "Cegqi::Lemma : enumerator : " << lem << std::endl;
  d_qe->getOutputChannel().lemma( lem );
  d_einfo[et].d_active_guard = eg;
}

void CegConjecturePbe::collectEnumeratorTypes( Node e, TypeNode tn ) {
  if( d_tinfo.find( tn )==d_tinfo.end() ){
    d_tinfo[tn].d_csol_status = 0;
    Trace("sygus-unif") << "Register enumerating type : " << tn << std::endl;
    Assert( tn.isDatatype() );
    const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
    Assert( dt.isSygus() );
    bool success = false;
    for( unsigned r=0; r<2; r++ ){
      for( unsigned j=0; j<dt.getNumConstructors(); j++ ){
        Node op = Node::fromExpr( dt[j].getSygusOp() );
        if( r==0 ){
          if( op.getKind() == kind::BUILTIN ){
            Kind sk = NodeManager::operatorToKind( op );
            if( sk==kind::ITE ){
              Trace("sygus-unif") << "...type " << dt.getName() << " has ITE, enumerate child types..." << std::endl;
              // we can do unification
              success = true;
              d_tinfo[tn].d_csol_op = Node::fromExpr( dt[j].getConstructor() );
              Assert( dt[j].getNumArgs()==3 );
              for( unsigned k=0; k<3; k++ ){
                TypeNode ct = TypeNode::fromType( dt[j][k].getRangeType() );
                Trace("sygus-unif") << "   Child type " << k << " : " << ((DatatypeType)ct.toType()).getDatatype().getName() << std::endl;
                d_tinfo[tn].d_csol_cts.push_back( ct );
                collectEnumeratorTypes( e, ct );
              }
              break;
            }
          }
        }else{
          if( dt[j].getNumArgs()>=3 ){
            // could be a defined ITE (this is a hack for ICFP benchmarks)
            std::vector< Node > utchildren;
            utchildren.push_back( Node::fromExpr( dt[j].getConstructor() ) );
            std::vector< Node > sks;
            std::vector< TypeNode > sktns;
            for( unsigned k=0; k<dt[j].getNumArgs(); k++ ){
              Type t = dt[j][k].getRangeType();
              TypeNode ttn = TypeNode::fromType( t );
              Node kv = NodeManager::currentNM()->mkSkolem( "ut", ttn );
              sks.push_back( kv );
              sktns.push_back( ttn );
              utchildren.push_back( kv );
            }
            Node ut = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, utchildren );
            std::vector< Node > echildren;
            echildren.push_back( Node::fromExpr( dt.getSygusEvaluationFunc() ) );
            echildren.push_back( ut );
            Node sbvl = Node::fromExpr( dt.getSygusVarList() );
            for( unsigned k=0; k<sbvl.getNumChildren(); k++ ){
              echildren.push_back( sbvl[k] );
            }
            Node eut = NodeManager::currentNM()->mkNode( kind::APPLY_UF, echildren );
            Trace("sygus-unif-debug") << "Test evaluation of " << eut << "..." << std::endl;
            eut = d_qe->getTermDatabaseSygus()->unfold( eut );
            Trace("sygus-unif-debug") << "...got " << eut << std::endl;
            if( eut.getKind()==kind::ITE ){
              success = true;
              std::vector< Node > vs;
              std::vector< Node > ss;
              std::map< Node, unsigned > templ_var_index;
              for( unsigned k=0; k<sks.size(); k++ ){
                echildren[1] = sks[k];
                Node esk = NodeManager::currentNM()->mkNode( kind::APPLY_UF, echildren );
                vs.push_back( esk );
                Node tvar = NodeManager::currentNM()->mkSkolem( "templ", esk.getType() );
                templ_var_index[tvar] = k;
                ss.push_back( tvar );
              }
              eut = eut.substitute( vs.begin(), vs.end(), ss.begin(), ss.end() );
              Trace("sygus-unif-debug") << "Defined constructor " << j << ", base term is " << eut << std::endl;
              //success if we can find a injection from ITE args to sygus args
              std::map< unsigned, unsigned > templ_injection;
              for( unsigned k=0; k<3; k++ ){
                if( !inferIteTemplate( k, eut[k], templ_var_index, templ_injection ) ){
                  Trace("sygus-unif-debug") << "...failed to find injection (range)." << std::endl;
                  success = false;
                  break;
                }
                if( templ_injection.find( k )==templ_injection.end() ){
                  Trace("sygus-unif-debug") << "...failed to find injection (domain)." << std::endl;
                  success = false;
                  break;
                }
              }
              if( success ){
                Trace("sygus-unif") << "...type " << dt.getName() << "has ITE-like constructor, enumerate child types..." << std::endl;
                d_tinfo[tn].d_csol_op = Node::fromExpr( dt[j].getConstructor() );
                for( unsigned k=0; k<3; k++ ){
                  Assert( templ_injection.find( k )!=templ_injection.end() );
                  unsigned sk_index = templ_injection[k];
                  //also store the template information, if necessary
                  Node teut = eut[k];
                  if( !teut.isVar() ){
                    d_tinfo[tn].d_template[k] = teut;
                    d_tinfo[tn].d_template_arg[k] = ss[sk_index];
                    Trace("sygus-unif") << "  Arg " << k << " : template : " << teut << ", arg " << ss[sk_index] << std::endl;
                  }else{
                    Assert( teut==ss[sk_index] );
                  }
                }
                // collect children types
                for( unsigned k=0; k<dt[j].getNumArgs(); k++ ){
                  Trace("sygus-unif") << "   Child type " << k << " : " << ((DatatypeType)sktns[k].toType()).getDatatype().getName() << std::endl;
                  d_tinfo[tn].d_csol_cts.push_back( sktns[k] );
                  collectEnumeratorTypes( e, sktns[k] );
                }
              }
            }
          }
        }
      }
      if( success ){
        break;
      }
    }
    if( !success ){
      Trace("sygus-unif") << "...consider " << dt.getName() << " a basic type" << std::endl;
    }
  }
}

bool CegConjecturePbe::inferIteTemplate( unsigned k, Node n, std::map< Node, unsigned >& templ_var_index, std::map< unsigned, unsigned >& templ_injection ){
  if( n.getNumChildren()==0 ){
    std::map< Node, unsigned >::iterator itt = templ_var_index.find( n );
    if( itt!=templ_var_index.end() ){
      unsigned kk = itt->second;
      std::map< unsigned, unsigned >::iterator itti = templ_injection.find( k );
      if( itti==templ_injection.end() ){
        templ_injection[k] = kk;
      }else if( itti->second!=kk ){
        return false;
      }
    }
    return true;
  }else{
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !inferIteTemplate( k, n[i], templ_var_index, templ_injection ) ){
        return false;
      }
    }
  }
  return true;
}



// ------------------------------------------- solution construction from enumeration

void CegConjecturePbe::getCandidateList( std::vector< Node >& candidates, std::vector< Node >& clist ) {
  for( unsigned i=0; i<candidates.size(); i++ ){
    Node v = candidates[i];
    std::map< Node, std::vector< Node > >::iterator it = d_esym_list.find( v );
    if( it!=d_esym_list.end() ){
      clist.insert( clist.end(), it->second.begin(), it->second.end() );
    }
  }
}

bool CegConjecturePbe::constructCandidates( std::vector< Node >& enums, std::vector< Node >& enum_values, 
                                            std::vector< Node >& candidates, std::vector< Node >& candidate_values, 
                                            std::vector< Node >& lems ) {
  Assert( enums.size()==enum_values.size() );
  Trace("sygus-pbe-enum") << "Register new enumerated values : " << std::endl;
  for( unsigned i=0; i<enums.size(); i++ ){
    Trace("sygus-pbe-enum") << "  " << enums[i] << " -> " << enum_values[i] << std::endl;
    addEnumeratedValue( enums[i], enum_values[i], lems );
  }
  for( unsigned i=0; i<candidates.size(); i++ ){
    //build decision tree for candidate
    //TODO
    return false;
  }
  return true;
}

bool CegConjecturePbe::addEnumeratedValue( Node x, Node v, std::vector< Node >& lems ) {
  std::map< Node, EnumInfo >::iterator it = d_einfo.find( x );
  Assert( it != d_einfo.end() );
  if( getGuardStatus( it->second.d_active_guard )==1 ){
    Assert( std::find( it->second.d_enum.begin(), it->second.d_enum.end(), v )==it->second.d_enum.end() );
    bool keep = true;
    Node e = it->second.d_parent_candidate;
    if( d_examples_out_invalid.find( e )!=d_examples_out_invalid.end() ){
      Trace("sygus-pbe-enum") << "Evaluation of " << e <<  " : ";
      //evaluate all input/output examples
      std::vector< bool > results;
      std::map< Node, std::vector< std::vector< Node > > >::iterator itx = d_examples.find( e );
      std::map< Node, std::vector< Node > >::iterator itxo = d_examples_out.find( e );
      Assert( itx!=d_examples.end() );
      Assert( itxo!=d_examples_out.end() );
      Assert( itx->second.size()==itxo->second.size() );
      TypeNode xtn = x.getType();
      Node bv = d_tds->sygusToBuiltin( v, xtn );
      for( unsigned j=0; j<itx->second.size(); j++ ){
        Node out = itxo->second[j];
        Node res = d_tds->evaluateBuiltin( xtn, bv, itx->second[j] );
        Assert( res.isConst() );
        Assert( out.isConst() );
        results.push_back( res==out );
        Trace("sygus-pbe-enum") << (res==out);
      }
      Trace("sygus-pbe-enum") << std::endl;
      //check subsumbed/subsuming
    }else{
      keep = false;
    }
    if( keep ){
      it->second.d_enum.push_back( v );
    }
    //exclude this value on subsequent iterations
    Node g = it->second.d_active_guard;
    Node exp = d_tds->getExplanationForConstantEquality( x, v );
    Node exlem = NodeManager::currentNM()->mkNode( kind::OR, g.negate(), exp.negate() );
    Trace("sygus-pbe-enum-lemma") << "CegConjecturePbe : enumeration exclude lemma : " << exlem << std::endl;
    lems.push_back( exlem );
    return keep;
  }else{
    Trace("sygus-pbe-enum-debug") << "  ...guard is inactive." << std::endl;
    return false;
  }
}

Node CegConjecturePbe::getNextDecisionRequest( unsigned& priority ) {
  for( std::map< Node, EnumInfo >::iterator it = d_einfo.begin(); it != d_einfo.end(); ++it ){
    Node g = it->second.d_active_guard;
    if( getGuardStatus( g )==0 ){
      Trace("cegqi-debug") << "CegConjecturePbe : Decide next on : " << g << "..." << std::endl;
      priority = 1;
      return g;
    }
  }
  return Node::null();
}

int CegConjecturePbe::getGuardStatus( Node g ) {
  bool value;
  if( d_qe->getValuation().hasSatValue( g, value ) ) {
    if( value ){
      return 1;
    }else{
      return -1;
    }
  }else{
    return 0;
  }
}

}
