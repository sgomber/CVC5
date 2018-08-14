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

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sample {

RewriteResponse TheorySampleRewriter::postRewrite(TNode node) 
{

  return RewriteResponse(REWRITE_DONE, node);
}


RewriteResponse TheorySampleRewriter::preRewrite(TNode node) 
{
  if( node.getKind()==SAMPLE_CHECK )
  {
    if( node[0].isConst() )
    {
      return RewriteResponse(REWRITE_DONE, node[0]);
    }
  }
  if( node.getKind()==SAMPLE_RUN )
  {
    if( node[0].isConst() )
    {
      return RewriteResponse(REWRITE_DONE, node[0]);
    }
  }
  return RewriteResponse(REWRITE_DONE, node);
}

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

