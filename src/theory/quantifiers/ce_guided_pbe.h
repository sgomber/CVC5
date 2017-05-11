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
  CegConjecture* d_parent;

  std::map< Node, bool > d_examples_invalid;
  std::map< Node, std::vector< std::vector< Node > > > d_examples;
  
  void collectExamples( Node n, std::map< Node, bool >& visited );
public:
  CegConjecturePbe( QuantifiersEngine * qe, CegConjecture * p );
  ~CegConjecturePbe();

  void initialize( Node q );
  bool getPbeExamples( Node v, std::vector< std::vector< Node > >& exs );
};


}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

#endif
