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
  quantifiers::TermDbSygus * d_tds;
  context::Context* d_context;
public:
  SygusSymBreakNew( quantifiers::TermDbSygus * tds, context::Context* c );
  ~SygusSymBreakNew();
  /** add tester */
  void addTester( int tindex, Node n, Node exp );

};



}
}
}

#endif
