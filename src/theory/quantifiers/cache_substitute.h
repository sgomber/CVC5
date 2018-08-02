/*********************                                                        */
/*! \file cache_substitute.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief cache_substitute
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CACHE_SUBSTITUTE_H
#define __CVC4__THEORY__QUANTIFIERS__CACHE_SUBSTITUTE_H

#include <map>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** CacheSubstitute
 * 
 * This class is useful when we need to compute many substitutions of a
 * fixed term over a variable domain.
 */
class CacheSubstitute
{
public:
  CacheSubstitute(){}
  /** initialize
   * 
   * This call initializes this class to cache information that is useful for
   * computing substitutions of the form n * { vars -> subs }, for some subs,
   * where * denotes application of substitution.
   */
  void initialize( Node n, const std::vector< Node >& vars );
  /** get substitute 
   * 
   * This computes n * { vars -> subs }, where this class was initialized with
   * the pair ( n, vars ), where * denotes application of substitution.
   */
  Node getSubstitute( const std::vector< Node >& subs );
private:
  /** the following information */
  std::vector< Kind > d_kinds;
  std::vector< std::vector< unsigned > > d_cons_ptr;
  std::vector< std::vector< Node > > d_data;
  std::vector< Node > d_data_out;
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H */
