/*********************                                                        */
/*! \file bv_subtheory_bitblast.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#include "cvc4_private.h"

#pragma once

#include "theory/bv/bitblaster_template.h"
#include "theory/bv/bv_subtheory.h"

namespace CVC4 {
namespace theory {
namespace bv {

class LazyBitblaster;
class AbstractionModule;
class BVQuickCheck;
class QuickXPlain;

/**
 * BitblastSolver
 */
class BitblastSolver : public SubtheorySolver {
  struct Statistics {
    IntStat d_numCallstoCheck;
    IntStat d_numBBLemmas;
    Statistics(const std::string &instanceName);
    ~Statistics();
  };
  /** Bitblaster */
  TLazyBitblaster* d_bitblaster;

  /** Nodes that still need to be bit-blasted */
  context::CDQueue<TNode> d_bitblastQueue;
  Statistics d_statistics;

  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
  NodeMap d_modelCache;
  context::CDO<bool> d_validModelCache;

  /** Queue for bit-blasting lemma atoms only in full check if we are sat */
  context::CDQueue<TNode> d_lemmaAtomsQueue;
  bool  d_useSatPropagation;
  AbstractionModule* d_abstractionModule;
  BVQuickCheck* d_quickCheck;
  QuickXPlain* d_quickXplain;
  //  Node getModelValueRec(TNode node);
  void setConflict(TNode conflict);
  
  bool isBbExpensive( TNode atom, std::map< TNode, bool >& visited );
  bool isBbExpensive( TNode atom ) {  
    std::map< TNode, bool > visited;
    return isBbExpensive( atom, visited );
  } 
  typedef context::CDHashMap<Node, Node, NodeHashFunction> CDNodeMap;
  CDNodeMap d_proxy_var;
  Node getBbCheapNode( TNode atom, std::map< TNode, Node >& visited );
  Node getBbCheapNode( TNode atom );
  CDNodeMap d_cfact_map;
  CDNodeMap d_cfact_map_rev;
  
  // for reducing bitblasted atoms
  ExtTheory * d_bb_extt;
  context::CDQueue<TNode> d_bbExpAtomsQueue;
  bool d_isComplete;
  
  bool do_bb_solve();
  void convertAtoms( std::vector<TNode>& conflictAtoms );
public:
  BitblastSolver(context::Context* c, TheoryBV* bv);
  ~BitblastSolver();

  void  preRegister(TNode node);
  bool  check(Theory::Effort e);
  void  explain(TNode literal, std::vector<TNode>& assumptions);
  EqualityStatus getEqualityStatus(TNode a, TNode b);
  void collectModelInfo(TheoryModel* m, bool fullModel);
  Node getModelValue(TNode node);
  bool isComplete()  { return d_isComplete; }
  void bitblastQueue();
  void setAbstraction(AbstractionModule* module);
  uint64_t computeAtomWeight(TNode atom);
  void setProofLog( BitVectorProof * bvp );
};

} /* namespace CVC4::theory::bv */
} /* namespace CVC4::theory */
} /* namespace CVC4 */
