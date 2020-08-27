/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Datatypes inference manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__DATATYPES__INFERENCE_MANAGER_H
#define CVC4__THEORY__DATATYPES__INFERENCE_MANAGER_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "theory/inference_manager_buffered.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

/**
 * The datatypes inference manager.
 */
class InferenceManager : public InferenceManagerBuffered
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
 public:
  InferenceManager(Theory& t,
                    TheoryState& state,
                    ProofNodeManager* pnm);
  ~InferenceManager() {}
protected:
  /** A cache of all lemmas sent */
  NodeSet d_lemmasSent;
};

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4

#endif
