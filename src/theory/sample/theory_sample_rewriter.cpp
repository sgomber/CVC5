/*********************                                                        */
/*! \file theory_sample_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** Implementation of the rewriter for theory of sampling.
 **/

#include "theory/sample/theory_sample_rewriter.h"

#include "expr/datatype.h"

namespace CVC4 {
namespace theory {
namespace sample {

/** is sample */
bool TheorySampleRewriter::isSampleType(TypeNode tn)
{
  if( !tn.isDatatype() )
  {
    return false;
  }
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  // FIXME
  if( !dt.isSygus() )
  {
    return false;
  }
  return true;
}

}/* CVC4::theory::sample namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

