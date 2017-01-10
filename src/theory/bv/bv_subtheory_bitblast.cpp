/*********************                                                        */
/*! \file bv_subtheory_bitblast.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Dejan Jovanovic, Tim King
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

#include "decision/decision_attributes.h"
#include "options/decision_options.h"
#include "options/bv_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/abstraction.h"
#include "theory/bv/bitblaster_template.h"
#include "theory/bv/bv_quick_check.h"
#include "theory/bv/bv_subtheory_bitblast.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "proof/proof_manager.h"
#include "proof/bitvector_proof.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::theory::bv::utils;

namespace CVC4 {
namespace theory {
namespace bv {

BitblastSolver::BitblastSolver(context::Context* c, TheoryBV* bv)
  : SubtheorySolver(c, bv),
    d_bitblaster(new TLazyBitblaster(c, bv, bv->getFullInstanceName() + "lazy")),
    d_bitblastQueue(c),
    d_statistics(bv->getFullInstanceName()),
    d_validModelCache(c, true),
    d_lemmaAtomsQueue(c),
    d_useSatPropagation(options::bitvectorPropagate()),
    d_abstractionModule(NULL),
    d_quickCheck(options::bitvectorQuickXplain() ? new BVQuickCheck("bb", bv) : NULL),
    d_quickXplain(options::bitvectorQuickXplain() ? new QuickXPlain("bb", d_quickCheck) :  NULL),
    d_proxy_var(bv->getUserContext()),
    d_cfact_map(bv->getUserContext()),
    d_cfact_map_rev(bv->getUserContext()),
    d_bbExpAtomsQueue(c),
    d_isComplete(true)
{

  d_bb_extt = new ExtTheory( bv );

}

BitblastSolver::~BitblastSolver() {
  delete d_quickXplain;
  delete d_quickCheck;
  delete d_bitblaster;
  delete d_bb_extt;
}

BitblastSolver::Statistics::Statistics(const std::string &instanceName)
  : d_numCallstoCheck(instanceName + "theory::bv::BitblastSolver::NumCallsToCheck", 0)
  , d_numBBLemmas(instanceName + "theory::bv::BitblastSolver::NumTimesLemmasBB", 0)
{
  smtStatisticsRegistry()->registerStat(&d_numCallstoCheck);
  smtStatisticsRegistry()->registerStat(&d_numBBLemmas);
}
BitblastSolver::Statistics::~Statistics() {
  smtStatisticsRegistry()->unregisterStat(&d_numCallstoCheck);
  smtStatisticsRegistry()->unregisterStat(&d_numBBLemmas);
}

void BitblastSolver::setAbstraction(AbstractionModule* abs) {
  d_abstractionModule = abs;
  d_bitblaster->setAbstraction(abs);
}

void BitblastSolver::preRegister(TNode node) {
  if ((node.getKind() == kind::EQUAL ||
       node.getKind() == kind::BITVECTOR_ULT ||
       node.getKind() == kind::BITVECTOR_ULE ||
       node.getKind() == kind::BITVECTOR_SLT ||
       node.getKind() == kind::BITVECTOR_SLE) &&
      !d_bitblaster->hasBBAtom(node)) {
    CodeTimer weightComputationTime(d_bv->d_statistics.d_weightComputationTimer);
    d_bitblastQueue.push_back(node);
    if ((options::decisionUseWeight() || options::decisionThreshold() != 0) &&
        !node.hasAttribute(decision::DecisionWeightAttr())) {
      node.setAttribute(decision::DecisionWeightAttr(),computeAtomWeight(node));
    }
  }
}

uint64_t BitblastSolver::computeAtomWeight(TNode node) {
  NodeSet seen;
  return d_bitblaster->computeAtomWeight(node, seen);
}

void BitblastSolver::explain(TNode literal, std::vector<TNode>& assumptions) {
  d_bitblaster->explain(literal, assumptions);
  convertAtoms(assumptions);
}

bool BitblastSolver::isBbExpensive( TNode atom, std::map< TNode, bool >& visited ) {
  if( visited.find( atom )==visited.end() ){
    visited[atom] = true;
    if( atom.getKind()==kind::BITVECTOR_MULT || atom.getKind()==kind::BITVECTOR_UDIV || 
        atom.getKind()==kind::BITVECTOR_UDIV || atom.getKind()==kind::BITVECTOR_UREM ||
        atom.getKind()==kind::BITVECTOR_SDIV || atom.getKind()==kind::BITVECTOR_SREM || atom.getKind()==kind::BITVECTOR_SMOD ){ //TODO
      return true;
    }else{
      for( unsigned i=0; i<atom.getNumChildren(); i++ ){
        if( isBbExpensive( atom[i], visited ) ){
          return true;
        }
      }
    }
  }
  return false;
}
Node BitblastSolver::getBbCheapNode( TNode atom, std::map< TNode, Node >& visited ) {
  std::map< TNode, Node >::iterator it = visited.find( atom );
  if( it!=visited.end() ){
    return it->second;
  }else{
    Node ret = atom;
    if( atom.getKind()==kind::BITVECTOR_MULT || atom.getKind()==kind::BITVECTOR_UDIV || 
        atom.getKind()==kind::BITVECTOR_UDIV || atom.getKind()==kind::BITVECTOR_UREM ||
        atom.getKind()==kind::BITVECTOR_SDIV || atom.getKind()==kind::BITVECTOR_SREM || atom.getKind()==kind::BITVECTOR_SMOD ){ //TODO
      CDNodeMap::const_iterator it = d_proxy_var.find( atom );
      if( it==d_proxy_var.end() ){
        Node k = NodeManager::currentNM()->mkSkolem( "k", atom.getType() );
        d_proxy_var[atom] = k;
        ret = k;
      }else{
        ret = (*it).second;
      }
    }else if( atom.getNumChildren()>0 ){
      std::vector< Node > children;
      if( atom.getMetaKind() == kind::metakind::PARAMETERIZED ){
        children.push_back( atom.getOperator() );
      }
      bool childChanged = false;
      for( unsigned i=0; i<atom.getNumChildren(); i++ ){
        Node c = getBbCheapNode( atom[i], visited );
        childChanged = childChanged || c!=atom[i];
        children.push_back( c );
      }
      if( childChanged ){
        ret = NodeManager::currentNM()->mkNode( atom.getKind(), children );
      }
    }
    visited[atom] = ret;
    return ret;
  }
}

Node BitblastSolver::getBbCheapNode( TNode atom ) {
  if( !options::bvLazyBbExp() ){
    return atom;
  }else{
    CDNodeMap::const_iterator it = d_cfact_map.find( atom );
    if( it==d_cfact_map.end() ){
      std::map< TNode, Node > visited;
      Node ret = getBbCheapNode( atom, visited );
      if( ret!=atom ){
        Trace("bvext") << "EXT : cheap form of " << atom << " : " << std::endl;
        Trace("bvext") << "                    " << ret << std::endl;
      }
      d_cfact_map[atom] = ret;
      d_cfact_map_rev[ret] = atom;
      return ret;
    }else{
      return (*it).second;    
    }
  }
}

void BitblastSolver::bitblastQueue() {
  while (!d_bitblastQueue.empty()) {
    TNode atom = d_bitblastQueue.front();
    d_bitblastQueue.pop();
    Debug("bv-bitblast-queue") << "BitblastSolver::bitblastQueue (" << atom << ")\n";
    if (options::bvAbstraction() &&
        d_abstractionModule->isLemmaAtom(atom)) {
      // don't bit-blast lemma atoms
      continue;
    }
    if( !utils::isBitblastAtom(atom) ){
      continue;
    }
    //check if it is an expensive atom
    /*
    if( isBbExpensive( atom ) ){
      Trace("bv-bb-extf") << "Expensive bitblast atom : " << atom << "." << std::endl;
      continue;
    }
    */
    Debug("bitblast-queue") << "Bitblasting atom " << atom <<"\n";
    {
      Node catom = getBbCheapNode( atom );
      if( catom!=atom ){
        Debug("bitblast-queue") << "*** EXT: consider instead its cheap form : " << catom << std::endl;
      }
      TimerStat::CodeTimer codeTimer(d_bitblaster->d_statistics.d_bitblastTimer);
      d_bitblaster->bbAtom(catom);
    }
    Debug("bitblast-queue") << "...finished Bitblasting atom " << atom <<"\n";
  }
}

bool BitblastSolver::check(Theory::Effort e) {
  Debug("bv-bitblast") << "BitblastSolver::check (" << e << ")\n";
  Assert(options::bitblastMode() == theory::bv::BITBLAST_MODE_LAZY);

  d_isComplete = true;
  ++(d_statistics.d_numCallstoCheck);

  Debug("bv-bitblast-debug") << "...process queue" << std::endl;
  //// Lazy bit-blasting
  // bit-blast enqueued nodes
  bitblastQueue();

  // Processing assertions
  while (!done()) {
    TNode fact = get();
    d_validModelCache = false;
    Debug("bv-bitblast") << "  fact " << fact << ")\n";

    //skip facts involving integer equalities (from bv2nat)
    if( !utils::isBitblastAtom( fact ) ){
      continue;
    }
    if (options::bvAbstraction()) {
      // skip atoms that are the result of abstraction lemmas
      if (d_abstractionModule->isLemmaAtom(fact)) {
        Debug("bv-bitblast") << "...lemma fact." << std::endl;
        d_lemmaAtomsQueue.push_back(fact);
        continue;
      }
    }
    /*
    if( isBbExpensive( fact ) ){
      Debug("bv-bitblast") << "...expensive fact : " << fact << "." << std::endl;
      //d_bbExpAtomsQueue.push_back( fact );
      d_bb_extt->registerTerm( fact, false );
      continue;
    }
    */

    if (!d_bv->inConflict() &&
        (!d_bv->wasPropagatedBySubtheory(fact) || d_bv->getPropagatingSubtheory(fact) != SUB_BITBLAST)) {
      // Some atoms have not been bit-blasted yet
      Node cfact = getBbCheapNode( fact );
      d_bitblaster->bbAtom(cfact);
      if( cfact!=fact ){ 
        Debug("bv-bitblast") << "*** EXT: assert instead its cheap form : " << cfact << std::endl;
        d_bbExpAtomsQueue.push_back( fact );
        d_bb_extt->registerTerm( fact, false );
      }
      // Assert to sat
      bool ok = d_bitblaster->assertToSat(cfact, d_useSatPropagation);
      if (!ok) {
        std::vector<TNode> conflictAtoms;
        d_bitblaster->getConflict(conflictAtoms);
        convertAtoms(conflictAtoms);
        setConflict(mkConjunction(conflictAtoms));
        return false;
      }
    }
  }

  Debug("bv-bitblast-debug") << "...do propagation" << std::endl;
  // We need to ensure we are fully propagated, so propagate now
  if (d_useSatPropagation) {
    d_bv->spendResource(1);
    bool ok = d_bitblaster->propagate();
    if (!ok) {
      std::vector<TNode> conflictAtoms;
      d_bitblaster->getConflict(conflictAtoms);
      convertAtoms(conflictAtoms);
      setConflict(mkConjunction(conflictAtoms));
      return false;
    }
  }

  // Solving
  Debug("bv-bitblast-debug") << "...do solving" << std::endl;
  if (e == Theory::EFFORT_FULL) {
    Debug("bitvector::bitblaster") << "BitblastSolver::addAssertions solving. \n";
    if( !do_bb_solve() ){
      return false;
    }
  }

  Debug("bv-bitblast-debug") << "...do abs bb" << std::endl;
  if (options::bvAbstraction() &&
      e == Theory::EFFORT_FULL &&
      d_lemmaAtomsQueue.size()) {

    // bit-blast lemma atoms
    while(!d_lemmaAtomsQueue.empty()) {
      TNode lemma_atom = d_lemmaAtomsQueue.front();
      d_lemmaAtomsQueue.pop();
      Assert( !utils::isBitblastAtom( lemma_atom ) );
      d_bitblaster->bbAtom(lemma_atom);
      // Assert to sat and check for conflicts
      bool ok = d_bitblaster->assertToSat(lemma_atom, d_useSatPropagation);
      if (!ok) {
        std::vector<TNode> conflictAtoms;
        d_bitblaster->getConflict(conflictAtoms);
        convertAtoms(conflictAtoms);
        setConflict(mkConjunction(conflictAtoms));
        return false;
      }
    }

    if( !do_bb_solve() ){
      ++(d_statistics.d_numBBLemmas);
      return false;
    }
  }

  Debug("bv-bitblast-debug") << "...do expensive bb" << std::endl;
  if( e == Theory::EFFORT_FULL ){
    //Trace("bv-bb-extf") << "Registering " << d_bbExpAtomsQueue.size() << " constraints with bitblast ExtTheory..." << std::endl;
    //while (!d_bbExpAtomsQueue.empty()) {
    //  TNode atom = d_bbExpAtomsQueue.front();
    //  d_bbExpAtomsQueue.pop();
    //  d_bb_extt->registerTerm( atom, false );
    //}
    std::vector< Node > nred;
    if( !d_bb_extt->doInferences( 0, nred ) ){
      Trace("bv-bb-extf") << "Unable to reduce " << nred.size() << " atoms " << std::endl;
      if( !nred.empty() ){
        for( unsigned j=0; j<nred.size(); j++ ){
          Trace("bv-bb-extf") << "  " << nred[j] << std::endl;
          d_bitblaster->bbAtom(nred[j]);
          d_bb_extt->markReduced(nred[j]);
          Assert(!d_bv->inConflict());
          bool ok = d_bitblaster->assertToSat(nred[j], d_useSatPropagation);
          if (!ok) {
            std::vector<TNode> conflictAtoms;
            d_bitblaster->getConflict(conflictAtoms);
            convertAtoms(conflictAtoms);
            setConflict(mkConjunction(conflictAtoms));
            return false;
          }
        }
        if( !do_bb_solve() ){
          return false;
        }
      }
    }else{
      d_isComplete = false;
      Trace("bv-bb-extf") << "...did inferences." << std::endl;
      return true;
    }
  }

  return true;
}

bool BitblastSolver::do_bb_solve() {
  Assert(!d_bv->inConflict());
  bool ok = d_bitblaster->solve();
  if (!ok) {
    std::vector<TNode> conflictAtoms;
    d_bitblaster->getConflict(conflictAtoms);
    convertAtoms(conflictAtoms);
    Node conflict = mkConjunction(conflictAtoms);
    setConflict(conflict);
  }
  return ok;
}

void BitblastSolver::convertAtoms( std::vector<TNode>& conflictAtoms ) {
  Trace("bvext-debug") << "Get conflict atoms, size = " << conflictAtoms.size() << std::endl;
  //map back to originals
  for( unsigned i=0; i<conflictAtoms.size(); i++ ){
    CDNodeMap::const_iterator it = d_cfact_map_rev.find( conflictAtoms[i] );
    if( it!=d_cfact_map_rev.end() ){
      conflictAtoms[i] = (*it).second;
    }
  }
}
  
EqualityStatus BitblastSolver::getEqualityStatus(TNode a, TNode b) {
  return d_bitblaster->getEqualityStatus(a, b);
}

void BitblastSolver::collectModelInfo(TheoryModel* m, bool fullModel) {
  return d_bitblaster->collectModelInfo(m, fullModel);
}

Node BitblastSolver::getModelValue(TNode node)
{
  if (d_bv->d_invalidateModelCache.get()) {
    d_bitblaster->invalidateModelCache();
  }
  d_bv->d_invalidateModelCache.set(false);
  Node val = d_bitblaster->getTermModel(node, true);
  return val;
}

void BitblastSolver::setConflict(TNode conflict) {
  Node final_conflict = conflict;
  if (options::bitvectorQuickXplain() &&
      conflict.getKind() == kind::AND) {
    // std::cout << "Original conflict " << conflict.getNumChildren() << "\n";
    final_conflict = d_quickXplain->minimizeConflict(conflict);
    //std::cout << "Minimized conflict " << final_conflict.getNumChildren() << "\n";
  }
  d_bv->setConflict(final_conflict);
}

void BitblastSolver::setProofLog( BitVectorProof * bvp ) {
  d_bitblaster->setProofLog( bvp );
  bvp->setBitblaster(d_bitblaster);
}

}/* namespace CVC4::theory::bv */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
