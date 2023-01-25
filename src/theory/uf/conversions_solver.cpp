/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of bit-vector conversions solver.
 */

#include "theory/uf/conversions_solver.h"

#include "theory/arith/arith_utilities.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_inference_manager.h"
#include "theory/theory_model.h"
#include "theory/theory_state.h"
#include "util/bitvector.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace uf {

ConversionsSolver::ConversionsSolver(Env& env,
                                     TheoryState& state,
                                     TheoryInferenceManager& im)
    : EnvObj(env),
      d_state(state),
      d_im(im),
      d_preRegistered(userContext()),
      d_reduced(userContext())
{
}

ConversionsSolver::~ConversionsSolver() {}

void ConversionsSolver::preRegisterTerm(TNode term)
{
  d_preRegistered.push_back(term);
}

void ConversionsSolver::check()
{
  Trace("bv-convs") << "Bitvector conversion terms : " << std::endl;
  Trace("bv-convs") << "ConversionsSolver: Check reductions for "
                    << d_preRegistered.size() << " terms" << std::endl;
  // check reductions for all bv conversion terms
  for (const Node& a : d_preRegistered)
  {
    checkReduction(a);
  }
}

void ConversionsSolver::checkReduction(Node n)
{
  Trace("bv-convs") << "Check reduction " << n << std::endl;
  if (d_reduced.find(n) != d_reduced.end())
  {
    Trace("bv-convs") << "...already reduced" << std::endl;
    return;
  }
  // check whether it already has the correct value in the model?
  Node val = d_state.getModel()->getValue(n);
  Node uval = d_state.getRepresentative(n);
  Trace("bv-convs-debug") << "  model value = " << val << std::endl;
  Trace("bv-convs-debug") << "          rep = " << uval << std::endl;
  if (val == uval)
  {
    // "model-based reduction" strategy, do not reduce things that already have
    // correct model values
    Trace("bv-convs") << "...already correct in model" << std::endl;
    return;
  }
  NodeManager * nm = NodeManager::currentNM();
  size_t w;
  Kind k = n.getKind();
  Node rn;
  if (k == BITVECTOR_TO_NAT)
  {
    w = n[0].getType().getBitVectorSize();
  }
  else
  {
    Assert (k == INT_TO_BITVECTOR);
    w = n.getOperator().getConst<IntToBitVector>().d_size;
  }
  if (w>1)
  {
    size_t halfW = w/2;
    Node c = nm->mkConstInt(Rational(Integer(2).pow(halfW)));
    if (k == BITVECTOR_TO_NAT)
    {
      Node rn1 = nm->mkNode(MULT, c, nm->mkNode(BITVECTOR_TO_NAT, bv::utils::mkExtract(n[0], w-1, halfW)));
      Node rn2 = nm->mkNode(BITVECTOR_TO_NAT, bv::utils::mkExtract(n[0], halfW-1, 0));
      rn = nm->mkNode(ADD, rn1, rn2);
    }
    else
    {
      Assert (k == INT_TO_BITVECTOR);
      Node iToBvop1 = nm->mkConst(IntToBitVector(w-halfW));
      Node rn1 = nm->mkNode(INT_TO_BITVECTOR, iToBvop1, nm->mkNode(INTS_DIVISION, n[0], c));
      Node iToBvop2 = nm->mkConst(IntToBitVector(halfW));
      Node rn2 = nm->mkNode(INT_TO_BITVECTOR, iToBvop2, nm->mkNode(INTS_MODULUS, n[0], c));
      rn = nm->mkNode(BITVECTOR_CONCAT, rn1, rn2);
    }
  }
  else
  {
    if (k == BITVECTOR_TO_NAT)
    {
      rn = arith::eliminateBv2Nat(n);
    }
    else
    {
      Assert (k == INT_TO_BITVECTOR);
      rn = arith::eliminateInt2Bv(n);
    }
  }
  Node lem = n.eqNode(rn);
  d_im.lemma(lem, InferenceId::UF_ARITH_BV_CONV_REDUCTION);
  d_reduced.insert(n);
  Trace("bv-convs") << "...do reduction" << std::endl;
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
