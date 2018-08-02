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

#ifndef __CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H
#define __CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H

#include <map>

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** CacheSubstitute
 * 
 */
class CacheSubstitute 
{
public:
  CacheSubstitute( QuantifiersEngine * qe );
  ~CacheSubstitute(){}
private:
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H */
