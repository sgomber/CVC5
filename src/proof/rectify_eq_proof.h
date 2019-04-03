/*********************                                                        */
/*! \file theory_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_RECTIFY_EQ_PROOF_H
#define __CVC4__THEORY_RECTIFY_EQ_PROOF_H

#include "theory/uf/equality_engine.h"

namespace CVC4 {

/** Rectifiable equality proof 
 * 
 * This class stores a EqProof object and manages its rectification via
 * a call to rectify below.
 */
class RectifiableEqProof
{
public:
  RectifiableEqProof(std::shared_ptr<theory::eq::EqProof> pf) : d_proof(pf), d_negStatus(0) {}
  /**
   * Helper function for ProofUF::toStreamRecLFSC and
   * ProofArray::toStreamRecLFSC
   * Inputs:
   *    - pf: equality engine proof
   *    - subTrans: main transitivity proof part
   *    - pPrettyPrinter: optional pretty printer for sub-proofs
   * returns:
   *    - the index of the contradicting node in pf.
   *    */
  static int rectify(
      theory::TheoryId theoryId,
      const theory::eq::EqProof& pf,
      std::shared_ptr<theory::eq::EqProof> subTrans,
      theory::eq::EqProof::PrettyPrinter* pPrettyPrinter = nullptr);  
  /** rectify this proof, if not already done so */
  void rectify(theory::TheoryId theoryId);
  /** get proof */
  theory::eq::EqProof * getProof() const;
  /** get sub transitivity proof */
  theory::eq::EqProof * getSubTransProof() const;
  /** get negation status */
  int getNegationStatus() const;
private:
  /** the input of this object */
  std::shared_ptr<theory::eq::EqProof> d_proof;
  /**  */
  std::shared_ptr<theory::eq::EqProof> d_subTrans;
  /** */
  int d_negStatus;
};

} /* CVC4 namespace */

#endif /* __CVC4__THEORY_RECTIFY_EQ_PROOF_H */
