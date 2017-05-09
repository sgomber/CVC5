/*********************                                                        */
/*! \file datatypes_sygus.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus utilities for theory of datatypes
 **
 ** Theory of datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__DATATYPES_SYGUS_NEW_H
#define __CVC4__THEORY__DATATYPES__DATATYPES_SYGUS_NEW_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/datatype.h"
#include "context/context.h"
#include "context/cdchunk_list.h"
#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "theory/datatypes/datatypes_sygus.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {
  class TermDbSygus;
} /* namespace quantifiers */

namespace datatypes {

class TheoryDatatypes;

class SygusSplitNew : public SygusSplitAbs
{
private:
  quantifiers::TermDbSygus * d_tds;
  std::map< Node, std::vector< Node > > d_splits;
public:
  SygusSplitNew( quantifiers::TermDbSygus * tds ) : d_tds( tds ){}
  virtual ~SygusSplitNew(){}
  /** get sygus splits */
  void getSygusSplits( Node n, const Datatype& dt, std::vector< Node >& splits, std::vector< Node >& lemmas );
};


class SygusSymBreakNew : public SygusSymBreakAbs
{
private:
  TheoryDatatypes * d_td;
  quantifiers::TermDbSygus * d_tds;
  context::Context* d_context;
  typedef context::CDHashMap< Node, int, NodeHashFunction > IntMap;
  typedef context::CDHashMap< Node, Node, NodeHashFunction > NodeMap;
  IntMap d_testers;
  NodeMap d_testers_exp;
  std::map< Node, Node > d_sel_to_anchor;
private:
  //list of all terms encountered in search at depth
  std::map< TypeNode, std::map< unsigned, std::vector< Node > > > d_search_terms;
  std::map< Node, bool > d_search_val_proc;
  std::map< TypeNode, std::map< Node, Node > > d_search_val;
  std::map< TypeNode, std::map< Node, unsigned > > d_search_val_sz;
  std::map< TypeNode, std::map< Node, Node > > d_search_val_b;
  std::map< Node, bool > d_is_top_level;
  std::map< TypeNode, std::map< unsigned, std::vector< Node > > > d_sb_lemmas;
  // register search term
  void registerSearchTerm( TypeNode tn, unsigned d, Node n, bool topLevel, std::vector< Node >& lemmas );
  bool registerSearchValue( Node n, Node nv, unsigned d, std::vector< Node >& lemmas );
  void registerSymBreakLemma( TypeNode tn, Node lem, unsigned sz, std::vector< Node >& lemmas );
private:
  std::map< TypeNode, std::map< int, Node > > d_simple_sb_pred;
  std::map< TypeNode, Node > d_simple_sb_pred_var;
  // user-context dependent if sygus-incremental
  std::map< Node, bool > d_simple_proc;
  //get simple symmetry breaking predicate
  Node getSimpleSymBreakPred( TypeNode tn, int tindex );
  TNode getSimpleSymBreakPredVar( TypeNode tn );
  bool considerArgKind( const Datatype& dt, const Datatype& pdt, TypeNode tn, TypeNode tnp, Kind k, Kind pk, int arg );
  bool considerConst( const Datatype& dt, const Datatype& pdt, TypeNode tn, TypeNode tnp, Node c, Kind pk, int arg );
private:
  //should be user-context dependent if sygus in incremental mode
  std::map< Node, bool > d_register_st;
  void registerSizeTerm( Node e );
private:
  std::map< unsigned, bool > d_search_size;
  unsigned d_curr_search_size;
  void incrementCurrentSearchSize( std::vector< Node >& lemmas );
private:
  unsigned processSelectorChain( Node n, std::map< TypeNode, Node >& top_level, 
                                 std::map< Node, unsigned >& tdepth, std::vector< Node >& lemmas );
public:
  SygusSymBreakNew( TheoryDatatypes * td, quantifiers::TermDbSygus * tds, context::Context* c );
  ~SygusSymBreakNew();
  /** add tester */
  void addTester( int tindex, TNode n, Node exp, std::vector< Node >& lemmas );
  void preRegisterTerm( TNode n );
  void notifySearchSize( unsigned s, std::vector< Node >& lemmas );
  void check( std::vector< Node >& lemmas );
};



}
}
}

#endif
