/*********************                                                        */
/*! \file ce_guided_pbe.h
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
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_PBE_H
#define __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_PBE_H

#include "context/cdhashmap.h"
#include "context/cdchunk_list.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class CegConjecture;
class CegConjecturePbe;
class CegEntailmentInfer;

class CegConjecturePbe {
private:
  QuantifiersEngine* d_qe;
  quantifiers::TermDbSygus * d_tds;
  CegConjecture* d_parent;
  Node d_true;
  Node d_false;

  std::map< Node, bool > d_examples_invalid;
  std::map< Node, bool > d_examples_out_invalid;
  std::map< Node, std::vector< std::vector< Node > > > d_examples;
  std::map< Node, std::vector< Node > > d_examples_out;
  std::map< Node, std::vector< Node > > d_examples_term;
  
  void collectExamples( Node n, std::map< Node, bool >& visited, bool hasPol, bool pol );
  bool d_is_pbe;
public:
  CegConjecturePbe( QuantifiersEngine * qe, CegConjecture * p );
  ~CegConjecturePbe();

  void initialize( Node n, std::vector< Node >& candidates );
  bool getPbeExamples( Node v, std::vector< std::vector< Node > >& exs, 
                       std::vector< Node >& exos, std::vector< Node >& exts);
  bool isPbe() { return d_is_pbe; }
private:  // for registration
  void collectEnumeratorTypes( Node e, TypeNode tn );
  void registerEnumerator( Node et, Node e, TypeNode tn, int j );

  /** register candidate conditional */
  bool inferIteTemplate( unsigned k, Node n, std::map< Node, unsigned >& templ_var_index, std::map< unsigned, unsigned >& templ_injection );  
  /** get guard status */
  int getGuardStatus( Node g );
public:
  class IndexFilter {
  public:
    IndexFilter(){}
    void mk( std::vector< bool >& vals, bool pol = true );
    std::map< unsigned, unsigned > d_next;
    unsigned start();
    unsigned next( unsigned i );
    void clear() { d_next.clear(); }
    bool isEq( std::vector< bool >& vs, bool v );
  };
private:
  // subsumption trie
  class SubsumeTrie {
  private:
    Node addTermInternal( Node t, std::vector< bool >& vals, bool pol, std::vector< Node >& subsumed, bool spol, IndexFilter * f, 
                          unsigned index, int status, bool checkExistsOnly, bool checkSubsume );
  public:
    SubsumeTrie(){}
    Node d_term;
    std::map< bool, SubsumeTrie > d_children;
    // adds term to the trie, removes based on subsumption
    Node addTerm( Node t, std::vector< bool >& vals, bool pol, std::vector< Node >& subsumed, IndexFilter * f = NULL );
    // adds condition to the trie (does not do subsumption)
    Node addCond( Node c, std::vector< bool >& vals, bool pol, IndexFilter * f = NULL );
    // returns the set of terms that are subsets of vals
    void getSubsumed( std::vector< bool >& vals, bool pol, std::vector< Node >& subsumed, IndexFilter * f = NULL );
    // returns the set of terms that are supersets of vals
    void getSubsumedBy( std::vector< bool >& vals, bool pol, std::vector< Node >& subsumed_by, IndexFilter * f = NULL );
  private:
    void getLeavesInternal( std::vector< bool >& vals, bool pol, std::map< int, std::vector< Node > >& v, IndexFilter * f, 
                            unsigned index, int status );
  public:
    // v[-1,1,0] -> children always false, always true, both
    void getLeaves( std::vector< bool >& vals, bool pol, std::map< int, std::vector< Node > >& v, IndexFilter * f = NULL );
  public:
    bool isEmpty() { return d_term.isNull() && d_children.empty(); }
    void clear() {
      d_term = Node::null();
      d_children.clear(); 
    }
  };

  class EnumInfo {
  private:
    /** an OR of all in d_enum_res */
    std::vector< bool > d_enum_total;
    bool d_enum_total_true;
    Node d_enum_solved;
  public:
    EnumInfo() : d_enum_total_true( false ), d_parent_arg(-1){}
    Node d_parent_candidate;
    TypeNode d_parent;
    int d_parent_arg;
    Node d_active_guard;
    std::vector< Node > d_enum_slave;
    /** values we have enumerated */
    std::vector< Node > d_enum_vals;
    std::vector< std::vector< bool > > d_enum_vals_res;
    std::vector< Node > d_enum_subsume;
    std::map< Node, unsigned > d_enum_val_to_index;
    SubsumeTrie d_term_trie;
  public:
    bool isBasic() { return d_parent_arg==-1; }
    bool isConditional() { return d_parent_arg==0; }
    void addEnumeratedValue( Node v, std::vector< bool >& results );
    void setSolved( Node slv );
    bool isCover();
    bool isSolved() { return !d_enum_solved.isNull(); }
    Node getSolved() { return d_enum_solved; }
  };
  std::map< Node, EnumInfo > d_einfo;
private:
  class CandidateInfo;
  class EnumTypeInfo {
  public:
    EnumTypeInfo() : d_parent( NULL ), d_csol_status(-1){}
    CandidateInfo * d_parent;
    Node d_enum;
    TypeNode d_this_type;
    /** conditional solutions */
    Node d_csol_op;
    std::vector< TypeNode > d_csol_cts;
    std::vector< Node > d_cenum;
    /** solution status */
    int d_csol_status;
    /** required for template solutions */
    std::map< unsigned, Node > d_template;
    std::map< unsigned, Node > d_template_arg;
    bool isCover( CegConjecturePbe * pbe, bool beneathCond, std::map< bool, std::map< TypeNode, bool > >& visited );
    bool isSolved( CegConjecturePbe * pbe );
    bool isConditionExpandable() { return !d_csol_op.isNull(); }
  };
  class CandidateInfo {
  public:
    CandidateInfo() : d_active( false ), d_check_dt( false ){}
    Node d_this_candidate;
    TypeNode d_root;
    std::map< TypeNode, EnumTypeInfo > d_tinfo;
    std::vector< Node > d_esym_list;
    std::map< TypeNode, Node > d_enum;
    bool d_active;
    bool d_check_dt;
    Node d_solution;
    void initialize( Node c );
    void initializeType( TypeNode tn );
    Node getRootEnumerator();
    bool isCover( TypeNode tn, CegConjecturePbe * pbe, bool beneathCond, std::map< bool, std::map< TypeNode, bool > >& visited );
    bool isCover( CegConjecturePbe * pbe );
  };
  //  candidate -> sygus type -> info
  std::map< Node, CandidateInfo > d_cinfo;

  /** add enumerated value */
  void addEnumeratedValue( Node x, Node v, std::vector< Node >& lems );
  
private:  
  // filtering verion
  /*
  class FilterSubsumeTrie {
  public:
    SubsumeTrie d_trie;
    IndexFilter d_filter;
    Node addTerm( Node t, std::vector< bool >& vals, std::vector< Node >& subsumed, bool checkExistsOnly = false ){
      return d_trie.addTerm( t, vals, subsumed, &d_filter, d_filter.start(), checkExistsOnly );
    }
  };
  */
  class UnifContext {
  public:
    IndexFilter d_filter;
    std::vector< bool > d_vals;
    bool updateContext( std::vector< bool >& vals, bool pol );
    class UEnumInfo {
    public:
      UEnumInfo() : d_status(-1){}
      int d_status;
      // enum val -> polarity -> solved
      std::map< Node, std::map< unsigned, Node > > d_look_ahead_sols;
    };
    // enumerator -> info
    std::map< Node, UEnumInfo > d_uinfo;
    void initialize( unsigned sz );
  };
  /** construct solution */
  Node constructDecisionTree( Node c );
  Node constructDecisionTree( Node c, Node e, UnifContext& x, int ind );
  Node constructBestSolvedTerm( std::vector< Node >& solved, UnifContext& x );
  Node constructBestSolvedConditional( std::vector< Node >& solved, UnifContext& x );
  Node constructBestConditional( std::vector< Node >& conds, UnifContext& x );
public:
  void registerCandidates( std::vector< Node >& candidates ); 
  void getCandidateList( std::vector< Node >& candidates, std::vector< Node >& clist );
  // lems and candidate values are outputs  
  bool constructCandidates( std::vector< Node >& enums, std::vector< Node >& enum_values, 
                            std::vector< Node >& candidates, std::vector< Node >& candidate_values, 
                            std::vector< Node >& lems );
public:
  Node getNextDecisionRequest( unsigned& priority );
};


}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

#endif
