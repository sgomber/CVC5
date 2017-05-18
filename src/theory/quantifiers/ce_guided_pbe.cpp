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
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
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
  bool typical_reg = true;
  if( options::sygusUnifCondSol() ){  
    if( candidates.size()==1 ){// conditional solutions for multiple function conjectures TODO?
      // collect a pool of types over which we will enumerate terms 
      Node e = candidates[0];
      //the candidate must be input/output examples
      if( d_examples_out_invalid.find( e )==d_examples_out_invalid.end() ){
        Assert( d_examples.find( e )!=d_examples.end() );
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
        typical_reg = false;
      }
    }
  }
  if( typical_reg ){
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
      Trace("sygus-pbe-enum") << "**** UNIF SOLVED : " << c << " = " << vc << std::endl;
      candidate_values.push_back( vc );
    }
  }
  return true;
}

void CegConjecturePbe::addEnumeratedValue( Node x, Node v, std::vector< Node >& lems ) {
  std::map< Node, EnumInfo >::iterator it = d_einfo.find( x );
  Assert( it != d_einfo.end() );
  if( getGuardStatus( it->second.d_active_guard )==1 ){
    Assert( std::find( it->second.d_enum.begin(), it->second.d_enum.end(), v )==it->second.d_enum.end() );
    bool keep = true;
    Node e = it->second.d_parent_candidate;
    if( d_examples_out_invalid.find( e )==d_examples_out_invalid.end() ){
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
        if( itv->second.isConditional() ){
          //if( cond_vals.size()!=2 ){
          //  // must discriminate
          //  Trace("sygus-pbe-enum") << "  ...fail : conditional is constant." << std::endl;
          //  keep = false;
          //}
          // must be unique up to examples
          Node val = itv->second.d_cond_trie.addCond( v, results, 0 );
          if( val==v ){
            if( Trace.isOn("sygus-pbe-enum") ){
              Node bv = d_tds->sygusToBuiltin( v, v.getType() );
              Trace("sygus-pbe-enum") << "  ...success!   value : " << bv << std::endl;
            }
          }else{
            Trace("sygus-pbe-enum") << "  ...fail : conditional is not unique" << std::endl;
            keep = false;
          }
        }else{
          if( cond_vals.find( true )!=cond_vals.end() ){
            //check subsumbed/subsuming
            if( cond_vals.find( false )==cond_vals.end() ){
              // it is the entire solution, we are done
              Trace("sygus-pbe-enum") << "  ...success, full solution!" << std::endl;
              itv->second.d_enum_solved = v;
            }else{
              std::vector< Node > subsume;
              Node val = itv->second.d_term_trie.addTerm( v, results, subsume );
              if( val==v ){
                Trace("sygus-pbe-enum") << "  ...success"; 
                if( !subsume.empty() ){
                  itv->second.d_enum_subsume.insert( itv->second.d_enum_subsume.end(), subsume.begin(), subsume.end() );
                  Trace("sygus-pbe-enum") << " and subsumed " << subsume.size() << " terms";
                }
                if( Trace.isOn("sygus-pbe-enum") ){
                  Node bv = d_tds->sygusToBuiltin( v, v.getType() );
                  Trace("sygus-pbe-enum") << "!   value : " << bv << std::endl;
                }
              }else{
                Assert( subsume.empty() );
                Trace("sygus-pbe-enum") << "  ...fail : subsumed" << std::endl;
              }
            }
          }else{
            Trace("sygus-pbe-enum") << "  ...fail : it does not satisfy examples." << std::endl;
            keep = false;
          }
        }
        if( keep ){
          itv->second.addEnumeratedValue( v, results );
          if( Trace.isOn("sygus-pbe-enum") ){
            if( !itv->second.isConditional() ){
              if( !prevIsCover && itv->second.isCover() ){
                Trace("sygus-pbe-enum") << "...success : Evaluation of " << xs << " now covers all examples." << std::endl;
              }
            }
          }
        }
      }
    }else{
      keep = false;
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
  d_enum.push_back( v );
  d_enum_res.push_back( results );
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

bool CegConjecturePbe::EnumTypeInfo::isCover( CegConjecturePbe * pbe, bool beneathCond, std::map< bool, std::map< TypeNode, bool > >& visited ) {
  if( beneathCond ){
    std::map< Node, EnumInfo >::iterator itn = pbe->d_einfo.find( d_enum );
    Assert( itn!=pbe->d_einfo.end() );
    if( itn->second.isCover() ){
      return true;
    }
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
        if( itnc->second.d_enum.empty() ){
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
      Trace("sygus-pbe-enum") << "...success : Candidate " << d_this_candidate << " is now solvable." << std::endl;
      d_active = true;
    }
  }
  return d_active;
}

bool CegConjecturePbe::EnumInfo::isCover() {
  Assert( !isConditional() );
  return d_enum_total_true;
}

bool CegConjecturePbe::EnumInfo::isSolved() { 
  return d_enum_solved.isNull(); 
}

Node CegConjecturePbe::CondTrie::addCond( Node cond, std::vector< bool >& vals, unsigned index, bool checkExistsOnly ) {
  if( index==vals.size() ){
    if( d_cond.isNull() && !checkExistsOnly ){
      d_cond = cond;
    }
    return d_cond;
  }else{
    if( checkExistsOnly ){
      std::map< bool, CondTrie >::iterator itc = d_children.find( vals[index] );
      if( itc!=d_children.end() ){
        return itc->second.addCond( cond, vals, index+1, checkExistsOnly );
      }else{
        return Node::null();
      }
    }else{
      return d_children[vals[index]].addCond( cond, vals, index+1, checkExistsOnly );
    }
  }
}

// status : 0 : exact, -1 : vals is subset, 1 : vals is superset
// is_term : 0 : term, -1 : negated condition, 1 : condition
Node CegConjecturePbe::SubsumeTrie::addTerm( Node t, std::vector< bool >& vals, std::vector< Node >& subsumed, IndexFilter * f, 
                                             int is_term, int status, unsigned index, bool checkExistsOnly ) {
  if( index==vals.size() ){
    if( is_term==0 ){
      // add terms before conditions
      Assert( d_cond.isNull() );
      if( status==0 ){
        if( d_term.isNull() && !checkExistsOnly ){
          d_term = t;
        }
      }else if( status==1 ){
        Assert( !d_term.isNull() );
        // found a subsumed term, remove it
        if( !d_term.isNull() ){
          subsumed.push_back( d_term );
          if( !checkExistsOnly ){
            d_term = Node::null();
          }
        }
        if( !d_cond.isNull() ){
          subsumed.push_back( d_cond );
        }
      }
      return d_term;
    }else{
      Assert( status!=1 );
      if( !d_term.isNull() ){
        //term is always true for this condition
        subsumed.push_back( d_term );
      }
      if( status==0 ){
        if( d_cond.isNull() && !checkExistsOnly ){
          d_cond = t;
        }
        return d_cond;
      }
      return Node::null();
    }
  }else{
    // the current value 
    bool cv = is_term==-1 ? !vals[index] : vals[index];
    std::vector< bool > check_subsumed_by;
    if( status==0 ){
      if( !cv ){
        check_subsumed_by.push_back( true );
      }
    }else if( status==-1 ){
      check_subsumed_by.push_back( true );
      if( !cv ){
        check_subsumed_by.push_back( false );
      }
    }
    // check for subsumed nodes
    if( !checkExistsOnly ){
      for( unsigned i=0; i<check_subsumed_by.size(); i++ ){
        bool csval = check_subsumed_by[i];
        // check if subsumed
        std::map< bool, SubsumeTrie >::iterator itc = d_children.find( csval );
        if( itc!=d_children.end() ){
          unsigned next_index = f ? f->next( index ) : index+1;
          Node ret = itc->second.addTerm( t, vals, subsumed, f, is_term, -1, next_index, checkExistsOnly );
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
      if( checkExistsOnly ){
        std::map< bool, SubsumeTrie >::iterator itc = d_children.find( cv );
        if( itc!=d_children.end() ){
          return itc->second.addTerm( t, vals, subsumed, f, is_term, 0, index+1, checkExistsOnly );
        }else{
          return Node::null();
        }
      }else{
        unsigned next_index = f ? f->next( index ) : index+1;
        ret = d_children[cv].addTerm( t, vals, subsumed, f, is_term, 0, next_index, checkExistsOnly );
      }
      if( is_term==0 && ret==t ){
        // check for subsuming
        if( cv ){
          check_subsume.push_back( false );
        }
      }
    }else if( status==1 ){
      Assert( is_term==0 );
      check_subsume.push_back( false );
      if( cv ){
        check_subsume.push_back( true );
      }
    }
    if( is_term==0 ){
      // check for subsumed terms
      for( unsigned i=0; i<check_subsume.size(); i++ ){
        bool csval = check_subsume[i];
        std::map< bool, SubsumeTrie >::iterator itc = d_children.find( csval );
        if( itc!=d_children.end() ){
          unsigned next_index = f ? f->next( index ) : index+1;
          itc->second.addTerm( t, vals, subsumed, f, is_term, 1, next_index, checkExistsOnly );
          // clean up
          if( itc->second.isEmpty() ){
            d_children.erase( csval );
          }
        }
      }
    }
    return ret;
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
  if( itc->second.isCover( this ) ){
    Node e = itc->second.getRootEnumerator();
    UnifContext x;
    // initialize with #examples
    Assert( d_examples.find( c )!=d_examples.end() );
    x.initialize( d_examples[c].size() );
    return constructDecisionTree( c, e, x );
  }else{
    return Node::null();
  }
}

Node CegConjecturePbe::constructDecisionTree( Node c, Node e, UnifContext& x ) {
  std::map< Node, EnumInfo >::iterator itn = d_einfo.find( e );
  Assert( itn!=d_einfo.end() );
  if( itn->second.isSolved() ){
    // this type has a complete solution
    return itn->second.d_enum_solved;
  }else{
    TypeNode etn = e.getType();
    
    // it has an enumerated value that is conditionally correct under the current assumptions ?
    std::vector< Node > subsumed;
    
    
    // if it base, then try to construct a conditional solution, if it exists
    
    if( x.d_uinfo.find( e )==x.d_uinfo.end() ){
      x.d_uinfo[e].d_status = 0;
      /*
      // for each conditional, check if there is an obvious solution
      for( std::map< TypeNode, EnumTypeInfo >::iterator it = itc->second.d_tinfo.begin(); 
           it != itc->second.d_tinfo.end(); ++it ){
        if( !it->second.d_csol_cts.empty() ){
          
        }
      }
      */
    }
    // look ahead conditional : choose conditionals that have solved terms in at least one branch
    
    
    // otherwise, guess a conditional
    
    return Node::null();
  }
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
