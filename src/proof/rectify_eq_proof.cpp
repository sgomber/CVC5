/*********************                                                        */
/*! \file rectify_eq_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "proof/rectify_eq_proof.h"

#include "proof/theory_proof.h"

namespace CVC4 {

void RectifiableEqProof::rectify(theory::TheoryId theoryId)
{
  if( !d_subTrans )
  {
    d_subTrans =
        std::make_shared<theory::eq::EqProof>();
    d_negStatus = TheoryProof::rectify(theoryId, *d_proof, d_subTrans);
  }
}

} /* namespace CVC4 */
