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
private:
  //list of all terms encountered in search at depth
  std::map< TypeNode, std::map< unsigned, std::vector< Node > > > d_search_terms;
  //list of all lemmas at a particular 
  std::map< TypeNode, std::map< unsigned, std::vector< Node > > > d_sb_lemmas;
  // get symmetry breaking lemmas for tester
  void getInitSymBreakLemmas( Node n );
private:
  //should be user-context dependent if sygus in incremental mode
  std::map< Node, bool > d_register;
  std::map< unsigned, bool > d_search_size;
  void registerTerm( Node e );
public:
  SygusSymBreakNew( TheoryDatatypes * td, quantifiers::TermDbSygus * tds, context::Context* c );
  ~SygusSymBreakNew();
  /** add tester */
  void addTester( int tindex, Node n, Node exp );
  void preRegisterTerm( TNode n );
  void notifySearchSize( unsigned s );
};



}
}
}

#endif
