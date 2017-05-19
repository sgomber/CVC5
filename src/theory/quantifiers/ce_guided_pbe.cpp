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

void indent( const char * c, int ind ) {
  if( Trace.isOn(c) ){
    for( int i=0; i<ind; i++ ){ 
      Trace(c) << "  "; 
    }
  } 
}
void print_val( const char * c, std::vector< bool >& vals, bool pol = true ){
  if( Trace.isOn(c) ){
    for( unsigned i=0; i<vals.size(); i++ ){
      Trace(c) << ( pol ? vals[i] : !vals[i] );
    }
  }
}

CegConjecturePbe::CegConjecturePbe(QuantifiersEngine* qe, CegConjecture* p)
    : d_qe(qe),
      d_parent(p){
  d_tds = d_qe->getTermDatabaseSygus();
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_is_pbe = false;
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
  
  //register candidates
  if( options::sygusUnifCondSol() ){  
    if( candidates.size()==1 ){// conditional solutions for multiple function conjectures TODO?
      // collect a pool of types over which we will enumerate terms 
      Node e = candidates[0];
      //the candidate must be input/output examples
      if( d_examples_out_invalid.find( e )==d_examples_out_invalid.end() ){
        Assert( d_examples.find( e )!=d_examples.end() );
        Trace("sygus-unif") << "It is input/output examples..." << std::endl;
        TypeNode etn = e.getType();
        d_cinfo[e].initialize( e );
        d_cinfo[e].d_root = etn;
        collectEnumeratorTypes( e, etn );
        // now construct the enumerators
        for( std::map< TypeNode, EnumTypeInfo >::iterator iti = d_cinfo[e].d_tinfo.begin(); iti != d_cinfo[e].d_tinfo.end(); ++iti ){
          TypeNode tn = iti->first;
          // register type
          Node ee = NodeManager::currentNM()->mkSkolem( "ee", tn );
          registerEnumerator( ee, e, tn, -1 );
          Trace("sygus-unif-debug") << "...enumerate " << ee << " for " << ((DatatypeType)tn.toType()).getDatatype().getName() << std::endl;
          iti->second.d_enum = ee;
        }
        for( std::map< TypeNode, EnumTypeInfo >::iterator iti = d_cinfo[e].d_tinfo.begin(); iti != d_cinfo[e].d_tinfo.end(); ++iti ){
          TypeNode tn = iti->first;
          for( unsigned j=0; j<iti->second.d_csol_cts.size(); j++ ){
            if( iti->second.d_template.find( j )!=iti->second.d_template.end() ){
              // it is templated, allocate a fresh variable
              Node et = NodeManager::currentNM()->mkSkolem( "et", iti->second.d_csol_cts[j] );
              Trace("sygus-unif-debug") << "...enumerate " << et << " of type " << ((DatatypeType)iti->second.d_csol_cts[j].toType()).getDatatype().getName();
              Trace("sygus-unif-debug") << " for arg " << j << " of " << ((DatatypeType)tn.toType()).getDatatype().getName() << std::endl;
              registerEnumerator( et, e, tn, j );
              iti->second.d_cenum.push_back( et );
            }else{
              // otherwise use the previous
              Assert( d_cinfo[e].d_enum.find( tn )!=d_cinfo[e].d_enum.end() );
              Node ee = d_cinfo[e].d_enum[tn];
              iti->second.d_cenum.push_back( ee );
            }
          }
        }
        d_is_pbe = true;
      }
    }
  }
  if( !d_is_pbe ){
    Trace("sygus-unif") << "Do not do PBE optimizations, register..." << std::endl;
    for( unsigned i=0; i<candidates.size(); i++ ){
      d_qe->getTermDatabaseSygus()->registerMeasuredTerm( candidates[i], candidates[i] );
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


void CegConjecturePbe::registerEnumerator( Node et, Node e, TypeNode tn, int j ) {
  d_einfo[et].d_parent_candidate = e;
  d_einfo[et].d_parent = tn;
  if( j>=0 ){
    d_einfo[et].d_parent_arg = j;
  }
  std::map< TypeNode, Node >::iterator itn = d_cinfo[e].d_enum.find( tn );
  if( itn==d_cinfo[e].d_enum.end() ){
    d_cinfo[e].d_enum[tn] = et;
    d_cinfo[e].d_esym_list.push_back( et );
    d_einfo[et].d_enum_slave.push_back( et );
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
    //register measured term
    d_qe->getTermDatabaseSygus()->registerMeasuredTerm( et, e );
  }else{
    Trace("sygus-unif-debug") << "Make " << et << " a slave of " << itn->second << std::endl;
    d_einfo[itn->second].d_enum_slave.push_back( et );
  }
}

void CegConjecturePbe::collectEnumeratorTypes( Node e, TypeNode tn ) {
  if( d_cinfo[e].d_tinfo.find( tn )==d_cinfo[e].d_tinfo.end() ){
    d_cinfo[e].initializeType( tn );
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
              d_cinfo[e].d_tinfo[tn].d_csol_op = Node::fromExpr( dt[j].getConstructor() );
              Assert( dt[j].getNumArgs()==3 );
              for( unsigned k=0; k<3; k++ ){
                TypeNode ct = TypeNode::fromType( dt[j][k].getRangeType() );
                Trace("sygus-unif") << "   Child type " << k << " : " << ((DatatypeType)ct.toType()).getDatatype().getName() << std::endl;
                d_cinfo[e].d_tinfo[tn].d_csol_cts.push_back( ct );
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
                d_cinfo[e].d_tinfo[tn].d_csol_op = Node::fromExpr( dt[j].getConstructor() );
                for( unsigned k=0; k<3; k++ ){
                  Assert( templ_injection.find( k )!=templ_injection.end() );
                  unsigned sk_index = templ_injection[k];
                  //also store the template information, if necessary
                  Node teut = eut[k];
                  if( !teut.isVar() ){
                    d_cinfo[e].d_tinfo[tn].d_template[k] = teut;
                    d_cinfo[e].d_tinfo[tn].d_template_arg[k] = ss[sk_index];
                    Trace("sygus-unif") << "  Arg " << k << " : template : " << teut << ", arg " << ss[sk_index] << std::endl;
                  }else{
                    Assert( teut==ss[sk_index] );
                  }
                }
                // collect children types
                for( unsigned k=0; k<dt[j].getNumArgs(); k++ ){
                  Trace("sygus-unif") << "   Child type " << k << " : " << ((DatatypeType)sktns[k].toType()).getDatatype().getName() << std::endl;
                  d_cinfo[e].d_tinfo[tn].d_csol_cts.push_back( sktns[k] );
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
    std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( v );
    if( it!=d_cinfo.end() ){
      clist.insert( clist.end(), it->second.d_esym_list.begin(), it->second.d_esym_list.end() );
    }
  }
}

bool CegConjecturePbe::constructCandidates( std::vector< Node >& enums, std::vector< Node >& enum_values, 
                                            std::vector< Node >& candidates, std::vector< Node >& candidate_values, 
                                            std::vector< Node >& lems ) {
  Assert( enums.size()==enum_values.size() );
  if( Trace.isOn("sygus-pbe-enum") ){
    Trace("sygus-pbe-enum") << "Register new enumerated values : " << std::endl;
    for( unsigned i=0; i<enums.size(); i++ ){
      Trace("sygus-pbe-enum") << "  " << enums[i] << " -> " << enum_values[i] << std::endl;
    }
  }
  for( unsigned i=0; i<enums.size(); i++ ){
    addEnumeratedValue( enums[i], enum_values[i], lems );
  }
  for( unsigned i=0; i<candidates.size(); i++ ){
    Node c = candidates[i];
    //build decision tree for candidate
    Node vc = constructDecisionTree( c );
    if( vc.isNull() ){     
      return false;
    }else{
      candidate_values.push_back( vc );
       
      //AlwaysAssert( false ); //FIXME
      //return false;
    }
  }
  return true;
}

void CegConjecturePbe::addEnumeratedValue( Node x, Node v, std::vector< Node >& lems ) {
  std::map< Node, EnumInfo >::iterator it = d_einfo.find( x );
  Assert( it != d_einfo.end() );
  if( getGuardStatus( it->second.d_active_guard )==1 ){
    Assert( std::find( it->second.d_enum_vals.begin(), it->second.d_enum_vals.end(), v )==it->second.d_enum_vals.end() );
    Node e = it->second.d_parent_candidate;
    if( d_examples_out_invalid.find( e )==d_examples_out_invalid.end() ){
      std::map< Node, CandidateInfo >::iterator itc = d_cinfo.find( e );
      Assert( itc != d_cinfo.end() );      
      TypeNode xtn = x.getType();
      Node bv = d_tds->sygusToBuiltin( v, xtn );
      std::map< Node, std::vector< std::vector< Node > > >::iterator itx = d_examples.find( e );
      std::map< Node, std::vector< Node > >::iterator itxo = d_examples_out.find( e );
      Assert( itx!=d_examples.end() );
      Assert( itxo!=d_examples_out.end() );
      Assert( itx->second.size()==itxo->second.size() );
      // notify all slaves
      Assert( !it->second.d_enum_slave.empty() );
      for( unsigned s=0; s<it->second.d_enum_slave.size(); s++ ){
        Node xs = it->second.d_enum_slave[s];
        std::map< Node, EnumInfo >::iterator itv = d_einfo.find( xs );
        Assert( itv!=d_einfo.end() );
        bool prevIsCover = false;
        if( itv->second.isConditional() ){
          Trace("sygus-pbe-enum") << " Cond-Eval of ";
        }else{
          Trace("sygus-pbe-enum") << "Evaluation of ";
          prevIsCover = itv->second.isCover();
        }
        Trace("sygus-pbe-enum")  << xs <<  " : ";
        //evaluate all input/output examples
        std::vector< bool > results;
        Node templ;
        TNode templ_var;
        if( itv->second.d_parent_arg>=0 ){
          TypeNode tnp = itv->second.d_parent;
          std::map< TypeNode, EnumTypeInfo >::iterator itp = d_cinfo[e].d_tinfo.find( tnp );
          Assert( itp!=d_cinfo[e].d_tinfo.end() );
          Assert( itp->second.d_template.find( itv->second.d_parent_arg )!=itp->second.d_template.end() );
          templ = itp->second.d_template[itv->second.d_parent_arg];
          Assert( itp->second.d_template_arg.find( itv->second.d_parent_arg )!=itp->second.d_template_arg.end() );
          templ_var = itp->second.d_template_arg[itv->second.d_parent_arg];
        }
        std::map< bool, bool > cond_vals;
        for( unsigned j=0; j<itx->second.size(); j++ ){
          Node out = itxo->second[j];
          Node res = d_tds->evaluateBuiltin( xtn, bv, itx->second[j] );
          Assert( res.isConst() );
          Assert( out.isConst() );
          if( !templ.isNull() ){
            TNode tres = res;
            res = templ.substitute( templ_var, res );
            res = Rewriter::rewrite( res );
            Assert( res.isConst() );
          }
          bool resb;
          if( itv->second.isConditional() ){
            resb = res==d_true;
            // it is a conditional
          }else{
            resb = res==out;
          }
          cond_vals[resb] = true;
          results.push_back( resb );
          Trace("sygus-pbe-enum") << resb;
        }
        bool keep = false;
        if( itv->second.isConditional() ){
          //if( cond_vals.size()!=2 ){
          //  // must discriminate
          //  Trace("sygus-pbe-enum") << "  ...fail : conditional is constant." << std::endl;
          //  keep = false;
          //}
          // must be unique up to examples
          Node val = itv->second.d_term_trie.addCond( v, results, true );
          if( val==v ){
            Trace("sygus-pbe-enum") << "  ...success!   add to DT pool : " << d_tds->sygusToBuiltin( v ) << std::endl;
            keep = true;
          }else{
            Trace("sygus-pbe-enum") << "  ...fail : conditional is not unique" << std::endl;
          }
          itc->second.d_cond_count++;
        }else{
          if( cond_vals.find( true )!=cond_vals.end() || cond_vals.empty() ){  // latter is the degenerate case of no examples
            //check subsumbed/subsuming
            std::vector< Node > subsume;
            if( cond_vals.find( false )==cond_vals.end() ){
              // it is the entire solution, we are done
              Trace("sygus-pbe-enum") << "  ...success, full solution added to DT pool : " << d_tds->sygusToBuiltin( v ) << std::endl;
              if( !itv->second.isSolved() ){
                itv->second.setSolved( v );
                // it subsumes everything
                itv->second.d_term_trie.clear();
                itv->second.d_term_trie.addTerm( v, results, true, subsume );
              }
              keep = true;
            }else{
              Node val = itv->second.d_term_trie.addTerm( v, results, true, subsume );
              if( val==v ){
                Trace("sygus-pbe-enum") << "  ...success"; 
                if( !subsume.empty() ){
                  itv->second.d_enum_subsume.insert( itv->second.d_enum_subsume.end(), subsume.begin(), subsume.end() );
                  Trace("sygus-pbe-enum") << " and subsumed " << subsume.size() << " terms";
                }
                Trace("sygus-pbe-enum") << "!   add to DT pool : " << d_tds->sygusToBuiltin( v ) << std::endl;
                keep = true;
              }else{
                Assert( subsume.empty() );
                Trace("sygus-pbe-enum") << "  ...fail : subsumed" << std::endl;
              }
            }
          }else{
            Trace("sygus-pbe-enum") << "  ...fail : it does not satisfy examples." << std::endl;
          }
        }
        if( keep ){
          // notify the parent to retry the build of DT
          itc->second.d_check_dt = true;
          itv->second.addEnumeratedValue( v, results );
          if( Trace.isOn("sygus-pbe-enum") ){
            if( !itv->second.isConditional() ){
              if( !prevIsCover && itv->second.isCover() ){
                Trace("sygus-pbe-enum") << "...DT : success : Evaluation of " << xs << " now covers all examples." << std::endl;
              }
            }
          }
        }
      }
    }else{
      Trace("sygus-pbe-enum-debug") << "  ...examples do not have output." << std::endl;
    }
    //exclude this value on subsequent iterations
    Node g = it->second.d_active_guard;
    Node exp = d_tds->getExplanationForConstantEquality( x, v );
    Node exlem = NodeManager::currentNM()->mkNode( kind::OR, g.negate(), exp.negate() );
    Trace("sygus-pbe-enum-lemma") << "CegConjecturePbe : enumeration exclude lemma : " << exlem << std::endl;
    lems.push_back( exlem );
  }else{
    Trace("sygus-pbe-enum-debug") << "  ...guard is inactive." << std::endl;
  }
}

void CegConjecturePbe::EnumInfo::addEnumeratedValue( Node v, std::vector< bool >& results ) {
  d_enum_val_to_index[v] = d_enum_vals.size();
  d_enum_vals.push_back( v );
  d_enum_vals_res.push_back( results );
  if( !isConditional() ){
    // compute 
    if( d_enum_total.empty() ){
      d_enum_total = results;
    }else if( !d_enum_total_true ){
      d_enum_total_true = true;
      Assert( d_enum_total.size()==results.size() );
      for( unsigned i=0; i<results.size(); i++ ){
        if( d_enum_total[i] || results[i] ){
          d_enum_total[i] = true;
        }else{
          d_enum_total[i] = false;
          d_enum_total_true = false;
        }
      }
    }
  }
}

void CegConjecturePbe::EnumInfo::setSolved( Node slv ) {
  d_enum_solved = slv;
  d_enum_total_true = true;
}

bool CegConjecturePbe::EnumInfo::isCover() {
  Assert( !isConditional() );
  return d_enum_total_true;
}

bool CegConjecturePbe::EnumTypeInfo::isCover( CegConjecturePbe * pbe, bool beneathCond, std::map< bool, std::map< TypeNode, bool > >& visited ) {
  std::map< Node, EnumInfo >::iterator itn = pbe->d_einfo.find( d_enum );
  Assert( itn!=pbe->d_einfo.end() );
  if( itn->second.isCover() ){
    return true;
  }
  if( !d_csol_op.isNull() ){
    Assert( d_csol_cts.size()==d_cenum.size() );
    for( unsigned i=0; i<d_csol_cts.size(); i++ ){
      TypeNode ct = d_csol_cts[i];
      Node ce = d_cenum[i];
      std::map< Node, EnumInfo >::iterator itnc = pbe->d_einfo.find( ce );
      Assert( itnc!=pbe->d_einfo.end() );
      if( i==0 ){
        // must be able to construct a condition (even if trivial)
        if( itnc->second.d_enum_vals.empty() ){
          return false;
        }
      }else{
        if( !itnc->second.isCover() ){
          // recurse : it could be conditionally constructable (cannot recurse if templated)  TODO?
          if( !itnc->second.isBasic() || !d_parent->isCover( ct, pbe, true, visited ) ){
            return false;
          }
        }
      }
    }
    return true;
  }
  return false;
}
    
void CegConjecturePbe::CandidateInfo::initialize( Node c ) {
  d_this_candidate = c;
  d_root = c.getType();
}

void CegConjecturePbe::CandidateInfo::initializeType( TypeNode tn ) {
  d_tinfo[tn].d_this_type = tn;
  d_tinfo[tn].d_parent = this;
}

Node CegConjecturePbe::CandidateInfo::getRootEnumerator() {
  std::map< TypeNode, Node >::iterator it = d_enum.find( d_root );
  Assert( it!=d_enum.end() );
  return it->second;
}


bool CegConjecturePbe::CandidateInfo::isCover( TypeNode tn, CegConjecturePbe * pbe, bool beneathCond, std::map< bool, std::map< TypeNode, bool > >& visited ) {
  std::map< TypeNode, bool >::iterator itv = visited[beneathCond].find( tn );
  if( itv==visited[beneathCond].end() ){
    visited[beneathCond][tn] = false;
    Assert( d_tinfo.find( tn )!=d_tinfo.end() );
    bool ret = d_tinfo[tn].isCover( pbe, beneathCond, visited );
    visited[beneathCond][tn] = ret;
    return ret;
  }else{
    return itv->second;
  }
}

bool CegConjecturePbe::CandidateInfo::isCover( CegConjecturePbe * pbe ) {
  if( !d_active ){
    std::map< bool, std::map< TypeNode, bool > > visited;
    if( isCover( d_root, pbe, false, visited ) ){
      Trace("sygus-pbe-enum") << "...DT : success : Candidate " << d_this_candidate << " is now solvable." << std::endl;
      d_active = true;
      d_check_dt = true;
    }
  }
  return d_active;
}



// status : 0 : exact, -1 : vals is subset, 1 : vals is superset
Node CegConjecturePbe::SubsumeTrie::addTermInternal( Node t, std::vector< bool >& vals, bool pol, 
                                                     std::vector< Node >& subsumed, bool spol, IndexFilter * f, 
                                                     unsigned index, int status, bool checkExistsOnly, bool checkSubsume ) {
  if( index==vals.size() ){
    if( status==0 ){
      // set the term if checkExistsOnly = false
      if( d_term.isNull() && !checkExistsOnly ){
        d_term = t;
      }
    }else if( status==1 ){
      Assert( checkSubsume );
      // found a subsumed term
      if( !d_term.isNull() ){
        subsumed.push_back( d_term );
        if( !checkExistsOnly ){
          // remove it if checkExistsOnly = false
          d_term = Node::null();
        }
      }else{
        Assert( false );
      }
    }else{
      Assert( !checkExistsOnly && checkSubsume );
    }
    return d_term;
  }else{
    // the current value 
    bool cv = pol ? vals[index] : !vals[index];
    // if checkExistsOnly = false, check if the current value is subsumed if checkSubsume = true, if so, don't add
    if( !checkExistsOnly && checkSubsume ){
      std::vector< bool > check_subsumed_by;
      if( status==0 ){
        if( !cv ){
          check_subsumed_by.push_back( spol );
        }
      }else if( status==-1 ){
        check_subsumed_by.push_back( spol );
        if( !cv ){
          check_subsumed_by.push_back( !spol );
        }
      }
      // check for subsumed nodes
      for( unsigned i=0; i<check_subsumed_by.size(); i++ ){
        bool csval = check_subsumed_by[i];
        // check if subsumed
        std::map< bool, SubsumeTrie >::iterator itc = d_children.find( csval );
        if( itc!=d_children.end() ){
          unsigned next_index = f ? f->next( index ) : index+1;
          Node ret = itc->second.addTermInternal( t, vals, pol, subsumed, spol, f, next_index, -1, checkExistsOnly, checkSubsume );
          // ret subsumes t
          if( !ret.isNull() ){
            return ret;
          }
        }
      }
    }
    Node ret;
    std::vector< bool > check_subsume;
    if( status==0 ){
      unsigned next_index = f ? f->next( index ) : index+1;
      if( checkExistsOnly ){
        std::map< bool, SubsumeTrie >::iterator itc = d_children.find( spol ? cv : !cv );
        if( itc!=d_children.end() ){
          ret = itc->second.addTermInternal( t, vals, pol, subsumed, spol, f, next_index, 0, checkExistsOnly, checkSubsume );
        }
      }else{
        Assert( spol );
        ret = d_children[cv].addTermInternal( t, vals, pol, subsumed, spol, f, next_index, 0, checkExistsOnly, checkSubsume );
        if( ret!=t ){
          // we were subsumed by ret, return
          return ret;
        }
      }
      if( checkSubsume ){
        // check for subsuming
        if( cv ){
          check_subsume.push_back( !spol );
        }
      }
    }else if( status==1 ){
      Assert( checkSubsume );
      check_subsume.push_back( !spol );
      if( cv ){
        check_subsume.push_back( spol );
      }
    }
    if( checkSubsume ){
      // check for subsumed terms
      for( unsigned i=0; i<check_subsume.size(); i++ ){
        bool csval = check_subsume[i];
        std::map< bool, SubsumeTrie >::iterator itc = d_children.find( csval );
        if( itc!=d_children.end() ){
          unsigned next_index = f ? f->next( index ) : index+1;
          itc->second.addTermInternal( t, vals, pol, subsumed, spol, f, next_index, 1, checkExistsOnly, checkSubsume );
          // clean up
          if( itc->second.isEmpty() ){
            Assert( !checkExistsOnly );
            d_children.erase( csval );
          }
        }
      }
    }
    return ret;
  }
}

Node CegConjecturePbe::SubsumeTrie::addTerm( Node t, std::vector< bool >& vals, bool pol, std::vector< Node >& subsumed, IndexFilter * f ) {
  unsigned start_index = f ? f->start() : 0;
  return addTermInternal( t, vals, pol, subsumed, true, f, start_index, 0, false, true );
}

Node CegConjecturePbe::SubsumeTrie::addCond( Node c, std::vector< bool >& vals, bool pol, IndexFilter * f ) {
  unsigned start_index = f ? f->start() : 0;
  std::vector< Node > subsumed;
  return addTermInternal( c, vals, pol, subsumed, true, f, start_index, 0, false, false );
}

void CegConjecturePbe::SubsumeTrie::getSubsumed( std::vector< bool >& vals, bool pol, std::vector< Node >& subsumed, IndexFilter * f ){
  unsigned start_index = f ? f->start() : 0;
  addTermInternal( Node::null(), vals, pol, subsumed, true, f, start_index, 0, true, true );
}

void CegConjecturePbe::SubsumeTrie::getSubsumedBy( std::vector< bool >& vals, bool pol, std::vector< Node >& subsumed_by, IndexFilter * f ){
  // flip polarities
  unsigned start_index = f ? f->start() : 0;
  addTermInternal( Node::null(), vals, !pol, subsumed_by, false, f, start_index, 0, true, true );
}

void CegConjecturePbe::SubsumeTrie::getLeavesInternal( std::vector< bool >& vals, bool pol, std::map< int, std::vector< Node > >& v, 
                                                       IndexFilter * f, unsigned index, int status ) {
  if( index==vals.size() ){
    Assert( !d_term.isNull() );
    Assert( std::find( v[status].begin(), v[status].end(), d_term )==v[status].end() );
    v[status].push_back( d_term );
  }else{
    bool cv = pol ? vals[index] : !vals[index];
    // filter should be for cv
    Assert( f==NULL || cv );
    for( std::map< bool, SubsumeTrie >::iterator it = d_children.begin(); it != d_children.end(); ++it ){
      int new_status = status;
      // if the current value is true
      if( cv ){
        if( status!=0 ){
          new_status = it->first ? 1 : -1;
          if( status!=-2 && new_status!=status ){
            new_status = 0;
          }
        }
      }
      unsigned next_index = f ? f->next( index ) : index+1;
      it->second.getLeavesInternal( vals, pol, v, f, next_index, new_status );
    }
  }
}

void CegConjecturePbe::SubsumeTrie::getLeaves( std::vector< bool >& vals, bool pol, std::map< int, std::vector< Node > >& v, IndexFilter * f ) {
  unsigned start_index = f ? f->start() : 0;
  getLeavesInternal( vals, pol, v, f, start_index, -2 );
}

void CegConjecturePbe::IndexFilter::mk( std::vector< bool >& vals, bool pol ) {
  Trace("sygus-pbe-debug") << "Make for : ";
  print_val( "sygus-pbe-debug", vals, pol );
  Trace("sygus-pbe-debug") << std::endl;
  
  unsigned curr_index = 0;
  while( curr_index<vals.size() && vals[curr_index]!=pol ){
    curr_index++;
  }
  d_next[0] = curr_index;
  Trace("sygus-pbe-debug") << "0 -> " << curr_index << std::endl;
  unsigned i = curr_index;
  while( i<vals.size() ){
    while( i<vals.size() && vals[i]!=pol ){
      i++;
    }
    i++;
    d_next[curr_index+1] = i;
    Trace("sygus-pbe-debug") << curr_index+1 << " -> " << i << std::endl;
    curr_index = i;
  }
  
  // verify it is correct
  unsigned j = start();
  for( unsigned k=0; k<j; k++ ){
    AlwaysAssert( vals[k]!=pol );
  }
  Trace("sygus-pbe-debug") << "...start : " << j << std::endl;
  unsigned counter = 0;
  while( j<vals.size() ){
    Trace("sygus-pbe-debug") << "...at : " << j << std::endl;
    AlwaysAssert( vals[j]==pol );
    unsigned jj = next( j );
    AlwaysAssert( jj>j );
    for( unsigned k=(j+1); k<jj; k++ ){
      AlwaysAssert( vals[k]!=pol );
    }
    AlwaysAssert( counter<=vals.size() );
    counter++;
    j = jj;
  }
  
  
}

unsigned CegConjecturePbe::IndexFilter::start() {
  std::map< unsigned, unsigned >::iterator it = d_next.find( 0 );
  if( it==d_next.end() ){
    return 0;
  }else{
    return it->second;
  }
}

unsigned CegConjecturePbe::IndexFilter::next( unsigned i ) {
  std::map< unsigned, unsigned >::iterator it = d_next.find( i+1 );
  if( it==d_next.end() ){
    return i+1;
  }else{
    return it->second;
  }      
}

bool CegConjecturePbe::IndexFilter::isEq( std::vector< bool >& vals, bool v ) {
  unsigned index = start();
  while( index<vals.size() ){
    if( vals[index]!=v ){
      return false;
    }
    index = next( index );
  }
  return true;
}

Node CegConjecturePbe::constructDecisionTree( Node c ){
  std::map< Node, CandidateInfo >::iterator itc = d_cinfo.find( c );
  Assert( itc!=d_cinfo.end() );
  if( !itc->second.d_solution.isNull() ){
    // already has a solution
    return itc->second.d_solution;
  }else{
    if( itc->second.isCover( this ) ){
      // only check if an enumerator updated
      if( itc->second.d_check_dt ){
        itc->second.d_check_dt = false;
        // try multiple times if we have done multiple conditions, due to non-determinism
        for( unsigned i=0; i<=itc->second.d_cond_count; i++ ){
          Trace("sygus-pbe-dt") << "ConstructDT for candidate: " << c << std::endl;
          Node e = itc->second.getRootEnumerator();
          UnifContext x;
          // initialize with #examples
          Assert( d_examples.find( c )!=d_examples.end() );
          x.initialize( d_examples[c].size() );
          Node vc = constructDecisionTree( c, e, x, 1 );
          if( !vc.isNull() ){
            Trace("sygus-pbe-enum") << "**** DT SOLVED : " << c << " = " << vc << std::endl;
            itc->second.d_solution = vc;
            return vc;
          }
        }
      }
    }
    return Node::null();
  }
}

Node CegConjecturePbe::constructBestSolvedTerm( std::vector< Node >& solved, UnifContext& x ){
  Assert( !solved.empty() );
  // TODO
  return solved[0];
}
Node CegConjecturePbe::constructBestSolvedConditional( std::vector< Node >& solved, UnifContext& x ){
  Assert( !solved.empty() );
  // TODO
  return solved[0];
}
Node CegConjecturePbe::constructBestConditional( std::vector< Node >& conds, UnifContext& x ) {
  Assert( !conds.empty() );
  // TODO
  double r = (double)(rand())/((double)(RAND_MAX));
  unsigned cindex = r*conds.size();
  if( cindex>conds.size() ){
    cindex = conds.size() - 1;
  }
  return conds[cindex];
}

Node CegConjecturePbe::constructDecisionTree( Node c, Node e, UnifContext& x, int ind ) {
  indent("sygus-pbe-dt", ind);
  Trace("sygus-pbe-dt") << "ConstructDT: enum: " << e << " in context ";
  print_val("sygus-pbe-dt-debug", x.d_vals);
  Trace("sygus-pbe-dt") << std::endl;
  std::map< Node, EnumInfo >::iterator itn = d_einfo.find( e );
  Assert( itn!=d_einfo.end() );
  Assert( !itn->second.isConditional() );
  Node ret_dt;
  if( itn->second.isSolved() ){
    // this type has a complete solution
    ret_dt = itn->second.getSolved();
    Assert( !ret_dt.isNull() );
    indent("sygus-pbe-dt-debug", ind);
    Trace("sygus-pbe-dt-debug") << "return DT: success : solved" << std::endl;
  }else{
    // it has an enumerated value that is conditionally correct under the current assumptions ?
    std::vector< Node > subsumed_by;
    itn->second.d_term_trie.getSubsumedBy( x.d_vals, true, subsumed_by );
    if( !subsumed_by.empty() ){
      ret_dt = constructBestSolvedTerm( subsumed_by, x );
      indent("sygus-pbe-dt-debug", ind);
      Trace("sygus-pbe-dt-debug") << "return DT: success : conditionally solved" << std::endl;
    }else if( itn->second.isBasic() ){
      // try to construct a conditional solution, if it exists
      TypeNode etn = e.getType();
      std::map< TypeNode, EnumTypeInfo >::iterator itt = d_cinfo[c].d_tinfo.find( etn );
      Assert( itt!=d_cinfo[c].d_tinfo.end() );
      if( itt->second.isConditionExpandable() ){
        // this is a conditionally expandable
        
        Assert( !itt->second.d_csol_op.isNull() );
        Assert( itt->second.d_cenum.size()==3 ); // for now, fix to 3 child ITEs
        
        std::vector< Node > dt_children;
        dt_children.push_back( itt->second.d_csol_op );
        
        // register the condition enumerator
        Node ce = itt->second.d_cenum[0];
        std::map< Node, EnumInfo >::iterator itnc = d_einfo.find( ce );
        Assert( itnc!=d_einfo.end() );
        if( x.d_uinfo.find( ce )==x.d_uinfo.end() ){
          Trace("sygus-pbe-dt-debug2") << "  reg : DT: Look for direct solutions for conditional enumerator " << ce << " ... " << std::endl;
          Assert( itnc->second.d_enum_vals.size()==itnc->second.d_enum_vals_res.size() );
          x.d_uinfo[ce].d_status = 0;
          for( unsigned i=1; i<=2; i++ ){
            Node te = itt->second.d_cenum[i];
            std::map< Node, EnumInfo >::iterator itnt = d_einfo.find( te );
            Assert( itnt!=d_einfo.end() );
            bool branch_pol = ( i==1 );
            // for each condition, get terms that satisfy it in this branch
            for( unsigned k=0; k<itnc->second.d_enum_vals.size(); k++ ){
              Node cond = itnc->second.d_enum_vals[k];
              std::vector< Node > solved;
              itnt->second.d_term_trie.getSubsumedBy( itnc->second.d_enum_vals_res[k], branch_pol, solved );
              Trace("sygus-pbe-dt-debug2") << "  reg : DT: " << d_tds->sygusToBuiltin( cond ) << " has " << solved.size() << " solutions in branch " << i << std::endl;
              if( !solved.empty() ){
                Node slv = constructBestSolvedTerm( solved, x );
                Trace("sygus-pbe-dt-debug") << "  reg : DT: ..." << d_tds->sygusToBuiltin( slv ) << " is a solution under branch " << i;
                Trace("sygus-pbe-dt-debug") << " of condition " << d_tds->sygusToBuiltin( cond ) << std::endl;
                x.d_uinfo[ce].d_look_ahead_sols[cond][i] = slv;
              }
            }
          }
        }
        
        // get the conditionals in the current context : they must be distinguishable
        std::map< int, std::vector< Node > > possible_cond;
        std::map< Node, int > solved_cond;  //stores branch
        //IndexFilter f;
        //f.mk( x.d_vals );
        itnc->second.d_term_trie.getLeaves( x.d_vals, true, possible_cond );
        
        std::map< int, std::vector< Node > >::iterator itpc = possible_cond.find( 0 );
        if( itpc!=possible_cond.end() ){
          indent("sygus-pbe-dt-debug", ind);
          Trace("sygus-pbe-dt-debug") << "DT : We have " << itpc->second.size() << " distinguishable conditionals." << std::endl;          
        
          Node split_cond;
          std::map< unsigned, Node > look_ahead_solved_children;
          
          // static look ahead conditional : choose conditionals that have solved terms in at least one branch
          std::map< int, std::vector< Node > > solved_cond;
          int solve_max = 0;
          for( unsigned k=0; k<itpc->second.size(); k++ ){
            Node cond = itpc->second[k];
            std::map< Node, std::map< unsigned, Node > >::iterator itla = x.d_uinfo[ce].d_look_ahead_sols.find( cond );
            if( itla!=x.d_uinfo[ce].d_look_ahead_sols.end() ){
              int nsolved = itla->second.size();
              solve_max = nsolved > solve_max ? nsolved : solve_max;
              solved_cond[nsolved].push_back( cond );
            }
          }
          int n = solve_max;
          while( n>0 ){
            if( !solved_cond[n].empty() ){
              split_cond = constructBestSolvedConditional( solved_cond[n], x );
              indent("sygus-pbe-dt-debug", ind);
              Trace("sygus-pbe-dt-debug") << "DT: choose solved conditional " << d_tds->sygusToBuiltin( split_cond ) << " with " << n << " solved children..." << std::endl;
              std::map< Node, std::map< unsigned, Node > >::iterator itla = x.d_uinfo[ce].d_look_ahead_sols.find( split_cond );
              Assert( itla!=x.d_uinfo[ce].d_look_ahead_sols.end() );
              for( std::map< unsigned, Node >::iterator itla2 = itla->second.begin(); itla2 != itla->second.end(); ++itla2 ){
                look_ahead_solved_children[ itla2->first ] = itla2->second;
              }
              break;
            }
            n--;
          }
          
          // dynamic look ahead conditional : compute if there are any solved terms in this branch  TODO
          if( ind>0 ){
            
          }
          
          // otherwise, guess a conditional
          if( split_cond.isNull() ){
            split_cond = constructBestConditional( itpc->second, x );
            Assert( !split_cond.isNull() );
            indent("sygus-pbe-dt-debug", ind);
            Trace("sygus-pbe-dt-debug") << "DT: choose random conditional " << d_tds->sygusToBuiltin( split_cond ) << std::endl;
          }
          
          // make the children of the decision tree
          dt_children.push_back( split_cond );
          
          bool success = true;
          Assert( itnc->second.d_enum_val_to_index.find( split_cond )!=itnc->second.d_enum_val_to_index.end() );
          unsigned split_cond_res_index = itnc->second.d_enum_val_to_index[split_cond];
          Assert( split_cond_res_index<itnc->second.d_enum_vals_res.size() );
          for( unsigned i=1; i<=2; i++ ){
            indent("sygus-pbe-dt-debug", ind);
            Trace("sygus-pbe-dt-debug") << "construct DT child #" << i << "..." << std::endl;
            std::map< unsigned, Node >::iterator itla = look_ahead_solved_children.find( i );
            if( itla!=look_ahead_solved_children.end() ){
              dt_children.push_back( itla->second );
              indent("sygus-pbe-dt-debug", ind+1);
              Trace("sygus-pbe-dt-debug") << "ConstructDT: look ahead solved : " << itla->second << std::endl;
            }else{
              // child enumerator
              Node te = itt->second.d_cenum[i];
              // update the context
              std::vector< bool > prev = x.d_vals;
              bool ret = x.updateContext( itnc->second.d_enum_vals_res[split_cond_res_index], i==1 );
              // must have updated the context
              AlwaysAssert( ret );
              Node rec_c = constructDecisionTree( c, te, x, ind+1 );
              if( rec_c.isNull() ){
                success = false;
                break;
              }else{
                dt_children.push_back( rec_c );
                x.d_vals = prev;
              }
            }
          }
          if( success ){
            ret_dt = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, dt_children );
            indent("sygus-pbe-dt-debug", ind);
            Trace("sygus-pbe-dt-debug") << "return DT: success : constructed conditional " << std::endl;
          }else{
            indent("sygus-pbe-dt-debug", ind);
            Trace("sygus-pbe-dt-debug") << "return DT: fail : child failed" << std::endl;
          }
        }else{
          // TODO : degenerate case where children have different types
          indent("sygus-pbe-dt-debug", ind);
          Trace("sygus-pbe-dt-debug") << "return DT: fail : cannot find a distinguishable condition" << std::endl;
        }
      }else{
        indent("sygus-pbe-dt-debug", ind);
        Trace("sygus-pbe-dt-debug") << "return DT: fail : not conditionally expandable" << std::endl;
      }
    }else{
      indent("sygus-pbe-dt-debug", ind);
      Trace("sygus-pbe-dt-debug") << "return DT: fail : non-basic" << std::endl;
    }
  }
  if( !ret_dt.isNull() ){
    Assert( ret_dt.getType()==e.getType() );
  }
  indent("sygus-pbe-dt", ind);
  Trace("sygus-pbe-dt") << "ConstructDT: returned " << ret_dt << std::endl;
  return ret_dt;
}

bool CegConjecturePbe::UnifContext::updateContext( std::vector< bool >& vals, bool pol ) {
  Assert( d_vals.size()==vals.size() );
  bool changed = false;
  for( unsigned i=0; i<vals.size(); i++ ){
    if( vals[i]!=pol ){
      if( d_vals[i] ){
        d_vals[i] = false;
        changed = true;
      }
    }
  }
  return changed;
}

void CegConjecturePbe::UnifContext::initialize( unsigned sz ) {
  for( unsigned i=0; i<sz; i++ ){
    d_vals.push_back( true );
  }
}
    
Node CegConjecturePbe::getNextDecisionRequest( unsigned& priority ) {
  for( std::map< Node, EnumInfo >::iterator it = d_einfo.begin(); it != d_einfo.end(); ++it ){
    Node g = it->second.d_active_guard;
    if( !g.isNull() ){
      if( getGuardStatus( g )==0 ){
        Trace("cegqi-debug") << "CegConjecturePbe : Decide next on : " << g << "..." << std::endl;
        priority = 1;
        return g;
      }
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
