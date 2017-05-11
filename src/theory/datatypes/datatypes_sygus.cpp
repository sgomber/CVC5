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
#include "theory/datatypes/datatypes_sygus.h"
#include "theory/quantifiers/term_database.h"
#include "theory/datatypes/theory_datatypes.h"
#include "theory/theory_model.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;

class ReqTrie {
public:
  ReqTrie() : d_req_kind( UNDEFINED_KIND ){}
  std::map< unsigned, ReqTrie > d_children;
  Kind d_req_kind;
  TypeNode d_req_type;
  Node d_req_const;
  void print( const char * c, int indent = 0 ){
    if( d_req_kind!=UNDEFINED_KIND ){
      Trace(c) << d_req_kind << " ";
    }else if( !d_req_type.isNull() ){
      Trace(c) << d_req_type;
    }else if( !d_req_const.isNull() ){
      Trace(c) << d_req_const;
    }else{
      Trace(c) << "_";
    }
    Trace(c) << std::endl;
    for( std::map< unsigned, ReqTrie >::iterator it = d_children.begin(); it != d_children.end(); ++it ){
      for( int i=0; i<=indent; i++ ) { Trace(c) << "  "; }
      Trace(c) << it->first << " : ";
      it->second.print( c, indent+1 );
    }
  }
  bool satisfiedBy( quantifiers::TermDbSygus * tdb, TypeNode tn ){
    if( d_req_kind!=UNDEFINED_KIND ){
      int c = tdb->getKindArg( tn, d_req_kind );
      if( c!=-1 ){
        const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
        for( std::map< unsigned, ReqTrie >::iterator it = d_children.begin(); it != d_children.end(); ++it ){
          if( it->first<dt[c].getNumArgs() ){
            TypeNode tnc = tdb->getArgType( dt[c], it->first );
            if( !it->second.satisfiedBy( tdb, tnc ) ){
              return false;
            }
          }else{
            return false;
          }
        }
        return true;
      }else{
        return false;
      }
    }else if( !d_req_const.isNull() ){
      return tdb->hasConst( tn, d_req_const );
    }else if( !d_req_type.isNull() ){
      return tn==d_req_type;
    }else{
      return true;
    }
  }
};

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


SygusSymBreakNew::SygusSymBreakNew( TheoryDatatypes * td, quantifiers::TermDbSygus * tds, context::Context* c ) : 
d_td( td ), d_tds( tds ), d_context( c ), 
d_testers( c ), d_testers_exp( c ), d_active_terms( c ), d_curr_search_size(0) {

}

SygusSymBreakNew::~SygusSymBreakNew() {

}

/** add tester */
void SygusSymBreakNew::addTester( int tindex, TNode n, Node exp, std::vector< Node >& lemmas ) {
  Node e = quantifiers::TermDbSygus::getAnchor( n );
  if( e.isVar() ){
    registerSizeTerm( e );
    //must be a sygus datatype
    if( d_register_st[e] ){
      Trace("sygus-sb-debug2") << "Sygus : process tester : " << exp << std::endl;
      if( d_active_terms.find( n )==d_active_terms.end() ) {
        d_testers[n] = tindex;
        d_testers_exp[n] = exp;
        
        // check if parent is active
        bool do_add = true;
        if( n.getKind()==kind::APPLY_SELECTOR_TOTAL ){
          NodeSet::const_iterator it = d_active_terms.find( n[0] );
          if( it==d_active_terms.end() ){
            do_add = false;
          }
        }
        if( do_add ){
          addTesterInternal( tindex, n, exp, lemmas );
        }
      }
    }
  }
}

void SygusSymBreakNew::addTesterInternal( int tindex, TNode n, Node exp, std::vector< Node >& lemmas ) {
  d_active_terms.insert( n );
  Trace("sygus-sb-debug2") << "Sygus : activate term : " << n << " : " << exp << std::endl;
  
  //collect all top-level terms 
  std::map< TypeNode, Node > top_level;
  std::map< Node, unsigned > tdepth;
  processSelectorChain( n, top_level, tdepth, lemmas );
  
  TypeNode ntn = n.getType();
  
  // now, add all applicable symmetry breaking lemmas for this term
  Assert( tdepth.find( n )!=tdepth.end() );
  unsigned d = tdepth[n];
  std::map< TypeNode, std::map< unsigned, std::vector< Node > > >::iterator its = d_sb_lemmas.find( ntn );
  if( its != d_sb_lemmas.end() ){
    TNode x = getSimpleSymBreakPredVar( ntn );
    //get symmetry breaking lemmas for this term 
    int max_sz = ((int)d_curr_search_size) - ((int)d);
    for( std::map< unsigned, std::vector< Node > >::iterator it = its->second.begin(); it != its->second.end(); ++it ){
      if( (int)it->first<=max_sz ){
        TNode t = n;
        for( unsigned k=0; k<it->second.size(); k++ ){
          Node lem = it->second[k];
          addSymBreakLemma( ntn, lem, x, t, it->first, d, lemmas );
        }
      }
    }
  }
    
  // process simple symmetry breaking
  if( d_simple_proc.find( exp )==d_simple_proc.end() ){
    d_simple_proc[exp] = true;
    TypeNode tn = n.getType();
    Node simple_sb_pred = getSimpleSymBreakPred( tn, tindex );
    if( !simple_sb_pred.isNull() ){
      TNode x = getSimpleSymBreakPredVar( tn );
      simple_sb_pred = simple_sb_pred.substitute( x, n );
      Node rlv = getRelevancyCondition( n );
      if( !rlv.isNull() ){
        simple_sb_pred = NodeManager::currentNM()->mkNode( kind::OR, rlv.negate(), simple_sb_pred ); 
      }
      lemmas.push_back( simple_sb_pred ); 
    }
  }
  
  // add back testers for the children if they exist
  const Datatype& dt = ((DatatypeType)ntn.toType()).getDatatype();
  for( unsigned j=0; j<dt[tindex].getNumArgs(); j++ ){
    Node sel = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[tindex].getSelectorInternal( ntn.toType(), j ) ), n );
    Trace("sygus-sb-debug2") << "  activate child sel : " << sel << std::endl;
    Assert( d_active_terms.find( sel )==d_active_terms.end() );
    IntMap::const_iterator itt = d_testers.find( sel );
    if( itt != d_testers.end() ){
      Assert( d_testers_exp.find( sel ) != d_testers_exp.end() );
      addTesterInternal( (*itt).second, sel, d_testers_exp[sel], lemmas );
    }
  }
}

Node SygusSymBreakNew::getRelevancyCondition( Node n ) {
  std::map< Node, Node >::iterator itr = d_rlv_cond.find( n );
  if( itr==d_rlv_cond.end() ){
    Node cond;
    if( n.getKind()==APPLY_SELECTOR_TOTAL ){
      TypeNode ntn = n[0].getType();
      Type nt = ntn.toType();
      const Datatype& dt = ((DatatypeType)nt).getDatatype();
      Expr selExpr = n.getOperator().toExpr();
      if( options::dtSharedSelectors() ){
        std::vector< Node > disj;
        bool excl = false;
        for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
          if( !d_tds->isGenericRedundant( ntn, i ) ){
            int sindexi = dt[i].getSelectorIndexInternal( nt, selExpr );
            if( sindexi!=-1 ){
              disj.push_back( DatatypesRewriter::mkTester( n[0], i, dt ) );
            }else{
              excl = true;
            }
          }
        }
        Assert( !disj.empty() );
        if( excl ){
          cond = disj.size()==1 ? disj[0] : NodeManager::currentNM()->mkNode( kind::OR, disj );
        }
      }else{
        int sindex = Datatype::cindexOf( selExpr );
        Assert( sindex!=-1 );
        cond = DatatypesRewriter::mkTester( n[0], sindex, dt );
      }
      Node c1 = getRelevancyCondition( n[0] );
      if( cond.isNull() ){
        cond = c1;
      }else if( !c1.isNull() ){
        cond = NodeManager::currentNM()->mkNode( kind::AND, cond, c1 );
      }
    }
    Trace("sygus-sb-debug2") << "Relevancy condition for " << n << " is " << cond << std::endl;
    d_rlv_cond[n] = cond;
    return cond;
  }else{
    return itr->second;
  }
}

Node SygusSymBreakNew::getSimpleSymBreakPred( TypeNode tn, int tindex ) {
  std::map< int, Node >::iterator it = d_simple_sb_pred[tn].find( tindex );
  if( it==d_simple_sb_pred[tn].end() ){
    Node n = getSimpleSymBreakPredVar( tn );
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
    Assert( tindex>=0 && tindex<(int)dt.getNumConstructors() );      
    Kind nk = d_tds->getArgKind( tn, tindex );
    //conjunctive conclusion of lemma
    std::vector< Node > sbp_conj;
    
    //fairness
    if( options::ceGuidedInstFair()==quantifiers::CEGQI_FAIR_DT_SIZE ){
      Node szl = NodeManager::currentNM()->mkNode( DT_SIZE, n );
      Node szr = NodeManager::currentNM()->mkNode( DT_SIZE, DatatypesRewriter::getInstCons( n, dt, tindex ) );
      szr = Rewriter::rewrite( szr );
      sbp_conj.push_back( szl.eqNode( szr ) );
      //sbp_conj.push_back( NodeManager::currentNM()->mkNode( kind::GEQ, szl, NodeManager::currentNM()->mkConst( Rational(0) ) ) );
    }
    
    //symmetry breaking
    if( options::sygusSymBreak() ){
      //get children
      std::vector< Node > children;
      for( unsigned j=0; j<dt[tindex].getNumArgs(); j++ ){
        Node sel = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[tindex].getSelectorInternal( tn.toType(), j ) ), n );
        Assert( sel.getType().isDatatype() );
        Assert( ((DatatypeType)sel.getType().toType()).getDatatype().isSygus() );
        children.push_back( sel );
        d_tds->registerSygusType( sel.getType() );
      }
      //builtin type
      TypeNode tnb = TypeNode::fromType( dt.getSygusType() );
      
      if( nk!=UNDEFINED_KIND ){
        // commutative operators 
        if( quantifiers::TermDb::isComm( nk ) ){
          if( children.size()==2 ){
            if( children[0].getType()==children[1].getType() ){
              std::vector< Node > comm_disj;
              // (1) size of left is greater than size of right
              Node sz_less = NodeManager::currentNM()->mkNode( GT, NodeManager::currentNM()->mkNode( DT_SIZE, children[0] ), 
                                                                   NodeManager::currentNM()->mkNode( DT_SIZE, children[1] ) );
              comm_disj.push_back( sz_less );
              // (2) ...or sizes are equal and first child is less by term order
              std::vector< Node > sz_eq_cases; 
              Node sz_eq = NodeManager::currentNM()->mkNode( EQUAL, NodeManager::currentNM()->mkNode( DT_SIZE, children[0] ), 
                                                                    NodeManager::currentNM()->mkNode( DT_SIZE, children[1] ) );
              sz_eq_cases.push_back( sz_eq );
              if( options::sygusOpt1() ){
                TypeNode tnc = children[0].getType();
                const Datatype& cdt = ((DatatypeType)(tnc).toType()).getDatatype();
                for( unsigned j=0; j<cdt.getNumConstructors(); j++ ){
                  if( !d_tds->isGenericRedundant( tnc, j ) ){
                    std::vector< Node > case_conj;
                    for( unsigned k=0; k<j; k++ ){
                      if( !d_tds->isGenericRedundant( tnc, k ) ){
                        case_conj.push_back( DatatypesRewriter::mkTester( children[1], k, cdt ).negate() );
                      }
                    }
                    if( !case_conj.empty() ){
                      Node corder = NodeManager::currentNM()->mkNode( kind::OR, DatatypesRewriter::mkTester( children[0], j, cdt ).negate(),
                                                                      case_conj.size()==1 ? case_conj[0] : NodeManager::currentNM()->mkNode( kind::AND, case_conj ) );
                      sz_eq_cases.push_back( corder );
                    }
                  }
                }
              }
              Node sz_eqc = sz_eq_cases.size()==1 ? sz_eq_cases[0] : NodeManager::currentNM()->mkNode( kind::AND, sz_eq_cases );
              comm_disj.push_back( sz_eqc );
              
              Node comm_sb = NodeManager::currentNM()->mkNode( kind::OR, comm_disj );
              sbp_conj.push_back( comm_sb );
            }
          }
        }
        // operators whose arguments are non-additive (e.g. should be different)
        if( children.size()==2 && children[0].getType()==children[1].getType() && children[0].getType()==tn ){
          bool argDeq = false;
          if( quantifiers::TermDb::isNonAdditive( nk ) ){
            argDeq = true;
          }else{
            //other cases of rewriting x k x -> x'
            Node req_const;
            if( nk==GT || nk==LT || nk==XOR || nk==MINUS || nk==BITVECTOR_SUB || nk==BITVECTOR_XOR || nk==BITVECTOR_UREM_TOTAL ){
              //must have the zero element
              req_const = d_tds->getTypeValue( tnb, 0 );
            }else if( nk==EQUAL || nk==LEQ || nk==GEQ || nk==BITVECTOR_XNOR ){
              req_const = d_tds->getTypeMaxValue( tnb );
            }
            //else if( nk==DIVISION_TOTAL || nk==BITVECTOR_UDIV_TOTAL ){
            //  req_const = d_tds->getTypeValue( tnb, 1 );
            //}
            if( !req_const.isNull() ){
              if( d_tds->hasConst( tn, req_const ) ){
                argDeq = true;
              }
            }
          }
          if( argDeq ){
            sbp_conj.push_back( children[0].eqNode( children[1] ).negate() );
          }
        }
        if( nk==ITE ){
          if( children[1].getType()==children[2].getType() ){
            if( !children[1].getType().getCardinality().isOne() ){
              sbp_conj.push_back( children[1].eqNode( children[2] ).negate() );
            }
          }
        }
        // division by zero
        if( nk==BITVECTOR_UDIV_TOTAL ){
          Assert( children.size()==2 );
          Node bv_zero = d_tds->getTypeValue( tnb, 0 );
          int zero_arg = d_tds->getConstArg( tn, bv_zero );
          if( zero_arg!=-1 ){
            // if denominator is zero, then consider only one numerator (TODO)
            
          }      
        }
        
        Trace("sygus-sb-simple-debug") << "Process arguments for " << tn << " : " << nk << " : " << std::endl;
        // singular arguments (e.g. 0 for mult) 
        // redundant arguments (e.g. 0 for plus, 1 for mult)
        // right-associativity
        // simple rewrites
        for( unsigned j=0; j<dt[tindex].getNumArgs(); j++ ){
          Node nc = children[j];
          TypeNode tnc = nc.getType();
          const Datatype& cdt = ((DatatypeType)(tnc).toType()).getDatatype();
          for( unsigned k=0; k<cdt.getNumConstructors(); k++ ){
            // if not already generic redundant
            if( !d_tds->isGenericRedundant( tnc, k ) ){
              Kind nck = d_tds->getArgKind( tnc, k );
              bool red = false;
              //check if the argument is redundant
              if( nck!=UNDEFINED_KIND ){
                Trace("sygus-sb-simple-debug") << "  argument " << j << " " << k << " is : " << nck << std::endl;
                red = !considerArgKind( cdt, dt, tnc, tn, nck, nk, j );
              }else{
                Node cc = d_tds->getArgConst( tnc, k  );
                if( !cc.isNull() ){
                  Trace("sygus-sb-simple-debug") << "  argument " << j << " " << k << " is constant : " << cc << std::endl;
                  red = !considerConst( cdt, dt, tnc, tn, cc, nk, j );
                }else{
                  //defined function?
                }
              }
              if( red ){
                Trace("sygus-sb-simple-debug") << "  ...redundant." << std::endl;
                sbp_conj.push_back( DatatypesRewriter::mkTester( nc, k, cdt ).negate() );
              }
            }
          }
        }
      }else{
        // defined function?
      }
    }
    
    Node sb_pred;
    if( !sbp_conj.empty() ){
      sb_pred = sbp_conj.size()==1 ? sbp_conj[0] : NodeManager::currentNM()->mkNode( kind::AND, sbp_conj );
      sb_pred = NodeManager::currentNM()->mkNode( kind::OR, DatatypesRewriter::mkTester( n, tindex, dt ).negate(), sb_pred );
      Trace("sygus-sb-simple") << "Simple predicate for " << tn << " index " << tindex << " (" << nk << ") : " << std::endl;
      Trace("sygus-sb-simple") << "   " << sb_pred << std::endl;
    }
    d_simple_sb_pred[tn][tindex] = sb_pred;
    return sb_pred;
  }else{
    return it->second;
  }
}

//this function gets all easy redundant cases, before consulting rewriters
bool SygusSymBreakNew::considerArgKind( const Datatype& dt, const Datatype& pdt, TypeNode tn, TypeNode tnp, Kind k, Kind pk, int arg ) {
  Assert( d_tds->hasKind( tn, k ) );
  Assert( d_tds->hasKind( tnp, pk ) );
  Trace("sygus-sb-debug") << "Consider sygus arg kind " << k << ", pk = " << pk << ", arg = " << arg << "?" << std::endl;
  int c = d_tds->getKindArg( tn, k );
  int pc = d_tds->getKindArg( tnp, pk );
  if( k==pk ){
    //check for associativity
    if( quantifiers::TermDb::isAssoc( k ) ){
      //if the operator is associative, then a repeated occurrence should only occur in the leftmost argument position
      int firstArg = d_tds->getFirstArgOccurrence( pdt[pc], tn );
      Assert( firstArg!=-1 );
      if( arg!=firstArg ){
        Trace("sygus-sb-simple") << "  sb-simple : do not consider " << k << " at child arg " << arg << " of " << k << " since it is associative, with first arg = " << firstArg << std::endl;
        return false;
      }else{
        return true;
      }
    }
  }
  //describes the shape of an alternate term to construct
  //  we check whether this term is in the sygus grammar below
  ReqTrie rt;
  bool rt_valid = false;
  
  //construct rt by cases
  if( pk==NOT || pk==BITVECTOR_NOT || pk==UMINUS || pk==BITVECTOR_NEG ){
    rt_valid = true;
    //negation normal form
    if( pk==k ){
      rt.d_req_type = d_tds->getArgType( dt[c], 0 );
    }else{
      Kind reqk = UNDEFINED_KIND;       //required kind for all children
      std::map< unsigned, Kind > reqkc; //required kind for some children
      if( pk==NOT ){
        if( k==AND ) {
          rt.d_req_kind = OR;reqk = NOT;
        }else if( k==OR ){
          rt.d_req_kind = AND;reqk = NOT;
        //AJR : eliminate this if we eliminate xor
        }else if( k==EQUAL ) {
          rt.d_req_kind = XOR;
        }else if( k==XOR ) {
          rt.d_req_kind = EQUAL;
        }else if( k==ITE ){
          rt.d_req_kind = ITE;reqkc[1] = NOT;reqkc[2] = NOT;
          rt.d_children[0].d_req_type = d_tds->getArgType( dt[c], 0 );
        }else if( k==LEQ || k==GT ){
          //  (not (~ x y)) ----->  (~ (+ y 1) x)
          rt.d_req_kind = k;
          rt.d_children[0].d_req_kind = PLUS;
          rt.d_children[0].d_children[0].d_req_type = d_tds->getArgType( dt[c], 1 );
          rt.d_children[0].d_children[1].d_req_const = NodeManager::currentNM()->mkConst( Rational( 1 ) );
          rt.d_children[1].d_req_type = d_tds->getArgType( dt[c], 0 );
          //TODO: other possibilities?
        }else if( k==LT || k==GEQ ){
          //  (not (~ x y)) ----->  (~ y (+ x 1))
          rt.d_req_kind = k;
          rt.d_children[0].d_req_type = d_tds->getArgType( dt[c], 1 );
          rt.d_children[1].d_req_kind = PLUS;
          rt.d_children[1].d_children[0].d_req_type = d_tds->getArgType( dt[c], 0 );
          rt.d_children[1].d_children[1].d_req_const = NodeManager::currentNM()->mkConst( Rational( 1 ) );
        }else{
          rt_valid = false;
        }
      }else if( pk==BITVECTOR_NOT ){
        if( k==BITVECTOR_AND ) {
          rt.d_req_kind = BITVECTOR_OR;reqk = BITVECTOR_NOT;
        }else if( k==BITVECTOR_OR ){
          rt.d_req_kind = BITVECTOR_AND;reqk = BITVECTOR_NOT;
        }else if( k==BITVECTOR_XNOR ) {
          rt.d_req_kind = BITVECTOR_XOR;
        }else if( k==BITVECTOR_XOR ) {
          rt.d_req_kind = BITVECTOR_XNOR;
        }else{
          rt_valid = false;
        }
      }else if( pk==UMINUS ){
        if( k==PLUS ){
          rt.d_req_kind = PLUS;reqk = UMINUS;
        }else{
          rt_valid = false;
        }
      }else if( pk==BITVECTOR_NEG ){
        if( k==PLUS ){
          rt.d_req_kind = PLUS;reqk = BITVECTOR_NEG;
        }else{
          rt_valid = false;
        }
      }
      if( rt_valid && ( reqk!=UNDEFINED_KIND || !reqkc.empty() ) ){
        int pcr = d_tds->getKindArg( tnp, rt.d_req_kind );
        if( pcr!=-1 ){
          Assert( pcr<(int)pdt.getNumConstructors() );
          //must have same number of arguments
          if( pdt[pcr].getNumArgs()==dt[c].getNumArgs() ){
            for( unsigned i=0; i<pdt[pcr].getNumArgs(); i++ ){
              Kind rk = reqk;
              if( reqk==UNDEFINED_KIND ){
                std::map< unsigned, Kind >::iterator itr = reqkc.find( i );
                if( itr!=reqkc.end() ){
                  rk = itr->second;
                }
              }
              if( rk!=UNDEFINED_KIND ){
                rt.d_children[i].d_req_kind = rk;
                rt.d_children[i].d_children[0].d_req_type = d_tds->getArgType( dt[c], i );
              }
            }
          }else{
            rt_valid = false;
          }
        }else{
          rt_valid = false;
        }
      }
    }
  }else if( k==MINUS || k==BITVECTOR_SUB ){
    if( pk==EQUAL || 
        pk==MINUS || pk==BITVECTOR_SUB || 
        pk==LEQ || pk==LT || pk==GEQ || pk==GT ){
      int oarg = arg==0 ? 1 : 0;
      //  (~ x (- y z))  ---->  (~ (+ x z) y)
      //  (~ (- y z) x)  ---->  (~ y (+ x z))
      rt.d_req_kind = pk;
      rt.d_children[arg].d_req_type = d_tds->getArgType( dt[c], 0 );
      rt.d_children[oarg].d_req_kind = k==MINUS ? PLUS : BITVECTOR_PLUS;
      rt.d_children[oarg].d_children[0].d_req_type = d_tds->getArgType( pdt[pc], oarg );
      rt.d_children[oarg].d_children[1].d_req_type = d_tds->getArgType( dt[c], 1 );
      rt_valid = true;
    }else if( pk==PLUS || pk==BITVECTOR_PLUS ){
      //  (+ x (- y z))  -----> (- (+ x y) z)
      //  (+ (- y z) x)  -----> (- (+ x y) z)
      rt.d_req_kind = pk==PLUS ? MINUS : BITVECTOR_SUB;
      int oarg = arg==0 ? 1 : 0;
      rt.d_children[0].d_req_kind = pk;
      rt.d_children[0].d_children[0].d_req_type = d_tds->getArgType( pdt[pc], oarg );
      rt.d_children[0].d_children[1].d_req_type = d_tds->getArgType( dt[c], 0 );
      rt.d_children[1].d_req_type = d_tds->getArgType( dt[c], 1 );
      rt_valid = true;
    }
  }else if( k==ITE ){
    if( pk!=ITE ){
      //  (o X (ite y z w) X')  -----> (ite y (o X z X') (o X w X'))
      rt.d_req_kind = ITE;
      rt.d_children[0].d_req_type = d_tds->getArgType( dt[c], 0 );
      unsigned n_args = pdt[pc].getNumArgs();
      for( unsigned r=1; r<=2; r++ ){
        rt.d_children[r].d_req_kind = pk;
        for( unsigned q=0; q<n_args; q++ ){
          if( (int)q==arg ){
            rt.d_children[r].d_children[q].d_req_type = d_tds->getArgType( dt[c], r );
          }else{
            rt.d_children[r].d_children[q].d_req_type = d_tds->getArgType( pdt[pc], q );
          }
        }
      }
      rt_valid = true;
      //TODO: this increases term size but is probably a good idea
    }
  }else if( k==NOT ){
    if( pk==ITE ){
      //  (ite (not y) z w)  -----> (ite y w z)
      rt.d_req_kind = ITE;
      rt.d_children[0].d_req_type = d_tds->getArgType( dt[c], 0 );
      rt.d_children[1].d_req_type = d_tds->getArgType( pdt[pc], 2 );
      rt.d_children[2].d_req_type = d_tds->getArgType( pdt[pc], 1 );
    }
  }
  Trace("sygus-sb-debug") << "Consider sygus arg kind " << k << ", pk = " << pk << ", arg = " << arg << "?" << std::endl;
  if( rt_valid ){
    rt.print("sygus-sb-debug");
    //check if it meets the requirements
    if( rt.satisfiedBy( d_tds, tnp ) ){
      Trace("sygus-sb-debug") << "...success!" << std::endl;
      Trace("sygus-sb-simple") << "  sb-simple : do not consider " << k << " as arg " << arg << " of " << pk << std::endl;
      //do not need to consider the kind in the search since there are ways to construct equivalent terms
      return false;
    }else{
      Trace("sygus-sb-debug") << "...failed." << std::endl;
    }
    Trace("sygus-sb-debug") << std::endl;
  }
  //must consider this kind in the search  
  return true;
}


bool SygusSymBreakNew::considerConst( const Datatype& dt, const Datatype& pdt, TypeNode tn, TypeNode tnp, Node c, Kind pk, int arg ) {
  Assert( d_tds->hasConst( tn, c ) );
  Assert( d_tds->hasKind( tnp, pk ) );
  int pc = d_tds->getKindArg( tnp, pk );
  Trace("sygus-sb-debug") << "Consider sygus const " << c << ", parent = " << pk << ", arg = " << arg << "?" << std::endl;
  if( d_tds->isIdempotentArg( c, pk, arg ) ){
    if( pdt[pc].getNumArgs()==2 ){
      int oarg = arg==0 ? 1 : 0;
      TypeNode otn = TypeNode::fromType( ((SelectorType)pdt[pc][oarg].getType()).getRangeType() );
      if( otn==tnp ){
        Trace("sygus-sb-simple") << "  sb-simple : " << c << " is idempotent arg " << arg << " of " << pk << "..." << std::endl;
        return false;
      }
    }
  }else{ 
    Node sc = d_tds->isSingularArg( c, pk, arg );
    if( !sc.isNull() ){
      if( d_tds->hasConst( tnp, sc ) ){
        Trace("sygus-sb-simple") << "  sb-simple : " << c << " is singular arg " << arg << " of " << pk << ", evaluating to " << sc << "..." << std::endl;
        return false;
      }
    }
  }
  ReqTrie rt;
  bool rt_valid = false;
  Node max_c = d_tds->getTypeMaxValue( c.getType() );
  if( pk==XOR || pk==BITVECTOR_XOR ){
    if( c==max_c ){
      rt.d_req_kind = pk==XOR ? NOT : BITVECTOR_NOT;
      rt_valid = true;
    }
  }
  if( rt_valid ){
    //check if satisfied
    if( rt.satisfiedBy( d_tds, tnp ) ){
      Trace("sygus-sb-simple") << "  sb-simple : do not consider const " << c << " as arg " << arg << " of " << pk << std::endl;
      //do not need to consider the constant in the search since there are ways to construct equivalent terms
      return false;
    }
  }
  return true;
}

TNode SygusSymBreakNew::getSimpleSymBreakPredVar( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_simple_sb_pred_var.find( tn );
  if( it==d_simple_sb_pred_var.end() ){
    Node x = NodeManager::currentNM()->mkSkolem( "x", tn );
    d_simple_sb_pred_var[tn] = x;
    return x;
  }else{
    return it->second;
  }
}

unsigned SygusSymBreakNew::processSelectorChain( Node n, std::map< TypeNode, Node >& top_level, std::map< Node, unsigned >& tdepth, std::vector< Node >& lemmas ) {
  unsigned ret = 0;
  if( n.getKind()==APPLY_SELECTOR_TOTAL ){
    ret = processSelectorChain( n[0], top_level, tdepth, lemmas );
  }
  TypeNode tn = n.getType();
  if( top_level.find( tn )==top_level.end() ){
    top_level[tn] = n;
    //tdepth[n] = ret;
    registerSearchTerm( tn, ret, n, true, lemmas );
  }else{
    registerSearchTerm( tn, ret, n, false, lemmas );
  }
  tdepth[n] = ret;
  return ret+1;
}

void SygusSymBreakNew::registerSearchTerm( TypeNode tn, unsigned d, Node n, bool topLevel, std::vector< Node >& lemmas ) {
  //register this term
  if( std::find( d_search_terms[tn][d].begin(), d_search_terms[tn][d].end(), n )==d_search_terms[tn][d].end() ){
    Trace("sygus-sb-debug") << "  register search term : " << n << " at depth " << d << ", type=" << tn << ", tl=" << topLevel << std::endl;
    d_search_terms[tn][d].push_back( n );
    if( topLevel ){
      d_is_top_level[n] = true;
    }
  }
}

bool SygusSymBreakNew::registerSearchValue( Node n, Node nv, unsigned d, std::vector< Node >& lemmas ) {
  Assert( n.getType()==nv.getType() );
  Assert( nv.getKind()==APPLY_CONSTRUCTOR );
  TypeNode tn = n.getType(); 
  if( nv.getNumChildren()>0 ){
    const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
    unsigned cindex = Datatype::indexOf( nv.getOperator().toExpr() );
    for( unsigned i=0; i<nv.getNumChildren(); i++ ){
      Node sel = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[cindex].getSelectorInternal( tn.toType(), i ) ), n );
      if( !registerSearchValue( sel, nv[i], d+1, lemmas ) ){
        return false;
      }
    }
  }
  if( d_is_top_level.find( n )!=d_is_top_level.end() ){
    if( d_search_val_proc.find( nv )==d_search_val_proc.end() ){
      d_search_val_proc[nv] = true;
      Trace("sygus-sb-debug") << "  ...register search value " << nv << ", type=" << tn << std::endl;
      Node bv = d_tds->sygusToBuiltin( nv, tn );
      Trace("sygus-sb-debug") << "  ......builtin is " << bv << std::endl;
      unsigned sz = d_tds->getSygusTermSize( nv );
      Node bvr = Rewriter::rewrite( bv );
      Trace("sygus-sb-debug") << "  ......rewrites to " << bvr << std::endl;
      std::map< Node, Node >::iterator itsv = d_search_val[tn].find( bvr );
      if( itsv==d_search_val[tn].end() ){
        d_search_val[tn][bvr] = nv;
        d_search_val_sz[tn][bvr] = sz;
      }else{
        Node bad_val = nv;
        Assert( d_search_val_sz[tn].find( bvr )!=d_search_val_sz[tn].end() );
        unsigned prev_sz = d_search_val_sz[tn][bvr];
        if( prev_sz>sz ){
          //swap : the excluded value is the previous
          d_search_val[tn][bvr] = nv;
          d_search_val_sz[tn][bvr] = sz;
          bad_val = itsv->second;
          sz = prev_sz;
        }
        Assert( d_tds->getSygusTermSize( bad_val )==(int)sz );
        if( Trace.isOn("sygus-sb-exc") ){
          Node prev_bv = d_tds->sygusToBuiltin( itsv->second, tn );
          Trace("sygus-sb-exc") << "  ......both " << prev_bv << " and " << bv << " rewrite to " << bvr << std::endl;
          Node bad_val_bv = d_tds->sygusToBuiltin( bad_val, tn );
          Trace("sygus-sb-exc") << "  ........exclude : " << bad_val_bv << std::endl;
        } 
        Node x = getSimpleSymBreakPredVar( tn );
        
        // do analysis of the evaluation  FIXME: does not work (evaluation is non-constant)
        /*
        const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
        std::vector< Node > echildren;
        echildren.push_back( Node::fromExpr( dt.getSygusEvaluationFunc() ) );
        echildren.push_back( x );
        Node sbvl = Node::fromExpr( dt.getSygusVarList() );
        for( unsigned k=0; k<sbvl.getNumChildren(); k++ ){
          echildren.push_back( sbvl[k] );
        }
        Node ex = NodeManager::currentNM()->mkNode( kind::APPLY_UF, echildren );
        Node eq = ex.eqNode( bvr );
        Trace("sygus-sb-exc") << "  ........evaluate : " << eq << std::endl;
        std::map< Node, Node > visited;
        std::map< Node, Node > vtm;
        std::map< Node, std::vector< Node > > exp;
        vtm[x] = nv;
        Node v = d_tds->crefEvaluate( eq, vtm, visited, exp );
        //Assert( v==NodeManager::currentNM()->mkConst( true ) );
        Assert( !exp[eq].empty() );
        Node lem = exp[eq].size()==1 ? exp[eq][0] : NodeManager::currentNM()->mkNode( kind::AND, exp[eq] );
        */
        std::vector< Node > exp;
        d_tds->getExplanationForConstantEquality( x, nv, exp );
        Node lem = exp.size()==1 ? exp[0] : NodeManager::currentNM()->mkNode( kind::AND, exp );
        lem = lem.negate();
        Trace("sygus-sb-exc") << "  ........exc lemma is " << lem << ", size = " << sz << std::endl;
        registerSymBreakLemma( tn, lem, sz, lemmas );
        return false;
      }
    }
  }
  return true;
}

void SygusSymBreakNew::registerSymBreakLemma( TypeNode tn, Node lem, unsigned sz, std::vector< Node >& lemmas ) {
  // lem holds for all terms of type tn, and is applicable to terms of size sz
  Trace("sygus-sb-debug") << "  register sym break lemma : " << lem << ", size " << sz << std::endl;
  d_sb_lemmas[tn][sz].push_back( lem );
  TNode x = getSimpleSymBreakPredVar( tn );
  int max_depth = ((int)d_curr_search_size)-((int)sz);
  for( int d=0; d<=max_depth; d++ ){
    std::map< unsigned, std::vector< Node > >::iterator itt = d_search_terms[tn].find( d );
    if( itt!=d_search_terms[tn].end() ){
      for( unsigned k=0; k<itt->second.size(); k++ ){
        TNode t = itt->second[k];  
        if( d_active_terms.find( t )!=d_active_terms.end() ){
          addSymBreakLemma( tn, lem, x, t, sz, d, lemmas );
        }
      }
    }
  }
}

void SygusSymBreakNew::addSymBreakLemma( TypeNode tn, Node lem, TNode x, TNode n, unsigned lem_sz, unsigned n_depth, std::vector< Node >& lemmas ) {
  Assert( d_active_terms.find( n )!=d_active_terms.end() );
  Assert( std::find( d_sb_lemmas[tn][lem_sz].begin(), d_sb_lemmas[tn][lem_sz].end(), lem )!=d_sb_lemmas[tn][lem_sz].end() );
  Assert( std::find( d_search_terms[tn][n_depth].begin(), d_search_terms[tn][n_depth].end(), n )!=d_search_terms[tn][n_depth].end() );
  // apply lemma
  Node slem = lem.substitute( x, n );
  Trace("sygus-sb-exc-debug") << "SymBreak lemma : " << slem << std::endl;
  Node rlv = getRelevancyCondition( n );
  if( !rlv.isNull() ){
    slem = NodeManager::currentNM()->mkNode( kind::OR, rlv.negate(), slem );
  }
  lemmas.push_back( slem );
}
  
void SygusSymBreakNew::preRegisterTerm( TNode n ) {
  if( n.isVar() ){
    registerSizeTerm( n );
  }
}

void SygusSymBreakNew::registerSizeTerm( Node e ) {
  if( d_register_st.find( e )==d_register_st.end() ){
    d_register_st[e] = false;
    if( !e.hasAttribute(TermSkolemAttribute()) ){
      if( e.getType().isDatatype() ){
        const Datatype& dt = ((DatatypeType)(e.getType()).toType()).getDatatype();
        if( dt.isSygus() ){
          Trace("sygus-sb") << "Sygus : register measured term : " << e << std::endl;
          d_register_st[e] = true;
          d_td->registerSygusMeasuredTerm( e );
        }
      }
    }
  }
}

void SygusSymBreakNew::notifySearchSize( unsigned s, Node exp, std::vector< Node >& lemmas ) {
  if( d_search_size.find( s )==d_search_size.end() ){
    d_search_size[s] = true;
    d_search_size_exp[s] = exp;
    Assert( s==0 || d_search_size.find( s-1 )!=d_search_size.end() );
    Trace("sygus-sb") << "SygusSymBreakNew:: now considering term measure : " << s << std::endl;
    Assert( s>=d_curr_search_size );
    while( s>d_curr_search_size ){
      incrementCurrentSearchSize( lemmas );
    }
    /*
    //re-add all testers (some may now be relevant) TODO
    for( IntMap::const_iterator it = d_testers.begin(); it != d_testers.end(); ++it ){
      Node n = (*it).first;
      NodeMap::const_iterator itx = d_testers_exp.find( n );
      if( itx!=d_testers_exp.end() ){
        int tindex = (*it).second;
        Node exp = (*itx).second;
        addTester( tindex, n, exp, lemmas );
      }else{
        Assert( false );
      }
    }
    */
  }
}

void SygusSymBreakNew::incrementCurrentSearchSize( std::vector< Node >& lemmas ) {
  d_curr_search_size++;
  Trace("sygus-sb-debug") << "  register search size " << d_curr_search_size << std::endl;
  for( std::map< TypeNode, std::map< unsigned, std::vector< Node > > >::iterator its = d_sb_lemmas.begin();
       its != d_sb_lemmas.end(); ++its ){
    TypeNode tn = its->first;
    TNode x = getSimpleSymBreakPredVar( tn );
    for( std::map< unsigned, std::vector< Node > >::iterator it = its->second.begin(); it != its->second.end(); ++it ){
      unsigned sz = it->first;
      int new_depth = ((int)d_curr_search_size) - ((int)sz);
      std::map< unsigned, std::vector< Node > >::iterator itt = d_search_terms[tn].find( new_depth );
      if( itt!=d_search_terms[tn].end() ){
        for( unsigned k=0; k<itt->second.size(); k++ ){
          TNode t = itt->second[k];
          if( d_active_terms.find( t )!=d_active_terms.end() ){
            for( unsigned j=0; j<it->second.size(); j++ ){
              Node lem = it->second[j];
              addSymBreakLemma( tn, lem, x, t, sz, new_depth, lemmas );
            }
          }
        }
      }
    }
  }
}

void SygusSymBreakNew::check( std::vector< Node >& lemmas ) {
  Trace("sygus-sb") << "SygusSymBreakNew::check" << std::endl;
  //construct current candidate terms
  /*
  std::map< Node, Node > cterm;
  std::map< Node, Node > waiting;
  std::map< Node, std::vector< Node > > cterm_exp;
  for( std::map< Node, bool >::iterator it = d_register_st.begin(); it != d_register_st.end(); ++it ){
    if( it->second ){
      cterm[ it->first ] = it->first;
      waiting[ it->first ] = it->first;
    }
  }
  bool success;
  do {
    success = false;
    for( IntMap::const_iterator iti = d_testers.begin(); iti != d_testers.end(); ++iti ){
      Node n = (*iti).first;
      int tindex = (*iti).second;
      std::map< Node, Node >::iterator itw = waiting.find( n );
      if( itw!=waiting.end() ){
        Node ct = itw->second;
        const Datatype& dt = ((DatatypeType)n.getType().toType()).getDatatype();
        Node ic = DatatypesRewriter::getInstCons( n, dt, tindex );
        std::vector< Node > ns;
        ns.push_back( n );
        std::vector< Node > ics;
        ics.push_back( ic );
        cterm[ct] = cterm[ct].substitute( ns.begin(), ns.end(), ics.begin(), ics.end() );
        //add to explanation
        NodeMap::const_iterator itte = d_testers_exp.find( n );
        if( itte!=d_testers_exp.end() ){
          cterm_exp[ct].push_back( (*itte).second );
        }else{
          Assert( false );
        }
        waiting.erase( n );
        for( unsigned j=0; j<ic.getNumChildren(); j++ ){
          waiting[ic[j]] = ct;
        }
        success = true;
      }
    }
  }while( success );
  
  for( std::map< Node, bool >::iterator it = d_register_st.begin(); it != d_register_st.end(); ++it ){
    if( it->second ){
      Node prog = it->first;
      Assert( cterm.find( prog )!=cterm.end() );
      Trace("sygus-sb") << "  val[" << prog << "] = " << cterm[prog] << std::endl;
      //convert to builtin
      Node bt = d_tds->sygusToBuiltin( prog, prog.getType() );
      //do rewriting techniques
      
    } 
  }
  */
  for( std::map< Node, bool >::iterator it = d_register_st.begin(); it != d_register_st.end(); ++it ){
    if( it->second ){
      Node prog = it->first;
      Node progv = d_td->getValuation().getModel()->getValue( prog );
      
      //debugging : ensure fairness was properly handled
      if( options::ceGuidedInstFair()==quantifiers::CEGQI_FAIR_DT_SIZE ){  
        Node prog_sz = NodeManager::currentNM()->mkNode( kind::DT_SIZE, prog );
        Node prog_szv = d_td->getValuation().getModel()->getValue( prog_sz );
        Node progv_sz = NodeManager::currentNM()->mkNode( kind::DT_SIZE, progv );
          
        Trace("sygus-sb") << "  Mv[" << prog << "] = " << progv << ", size = " << prog_szv << std::endl;
        if( prog_szv.getConst<Rational>().getNumerator().toUnsignedInt() > d_curr_search_size ){
          debugTermSize( prog, 0 );
          AlwaysAssert( false );
          Node szlem = NodeManager::currentNM()->mkNode( kind::OR, prog.eqNode( progv ).negate(),
                                                                   prog_sz.eqNode( progv_sz ) );
          Trace("sygus-sb-warn") << "SygusSymBreak : WARNING : adding size correction : " << szlem << std::endl;
          lemmas.push_back( szlem );                                                     
          return;
        }
        //AlwaysAssert( prog_szv.getConst<Rational>().getNumerator().toUnsignedInt() <= d_curr_search_size );
      }
      if( options::sygusSymBreakDynamic() ){
        if( !registerSearchValue( prog, progv, 0, lemmas ) ){
          break;
        }
      }
    }
  }
}

void SygusSymBreakNew::getPossibleCons( const Datatype& dt, TypeNode tn, std::vector< bool >& pcons ) {
  Assert( pcons.size()==dt.getNumConstructors() );
  d_tds->registerSygusType( tn );
  for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
    if( d_tds->isGenericRedundant( tn, i ) ){
      pcons[i] = false;
    }
  }
}

void SygusSymBreakNew::debugTermSize( Node n, int ind ) {
  Node progv = d_td->getValuation().getModel()->getValue( n );
  Assert( progv.getKind()==kind::APPLY_CONSTRUCTOR );
  Node prog_sz = NodeManager::currentNM()->mkNode( kind::DT_SIZE, n );
  Node prog_szv = d_td->getValuation().getModel()->getValue( prog_sz );
  for( int i=0; i<ind; i++ ){
    Trace("sygus-sb") << "  ";
  }
  Trace("sygus-sb") << n << " : " << progv << " : " << prog_szv << std::endl;
  
  TypeNode tn = n.getType();
  const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
  int cindex = Datatype::indexOf( progv.getOperator().toExpr() );
  Node tst = DatatypesRewriter::mkTester( n, cindex, dt );
  bool hastst = d_td->getValuation().getModel()->hasTerm( tst );
  Node tstrep = d_td->getValuation().getModel()->getRepresentative( tst );
  if( !hastst || tstrep!=NodeManager::currentNM()->mkConst( true ) ){
    Trace("sygus-sb") << "- has tester : " << tst << " : " << ( hastst ? "true" : "false" );
    Trace("sygus-sb") << ", value=" << tstrep << std::endl;
  }
  for( unsigned i=0; i<progv.getNumChildren(); i++ ){
    Node sel = NodeManager::currentNM()->mkNode( kind::APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[cindex].getSelectorInternal( tn.toType(), i ) ), n );
    debugTermSize( sel, ind+1 );
  }
}

