/*********************                                                        */
/*! \file sat_relevancy.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sat relevancy module
 **/

#include "cvc5_private.h"

#ifndef CVC5__PROP__SAT_RELEVANCY_H
#define CVC5__PROP__SAT_RELEVANCY_H

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "context/cdqueue.h"
#include "expr/node.h"
#include "options/prop_options.h"
#include "prop/sat_solver.h"
#include "smt/env_obj.h"
#include "theory/theory.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {

class DecisionEngine;
class TheoryEngine;
class Env;

namespace prop {

class CnfStream;
class CDCLTSatSolverInterface;

/** Properties of atoms (which can also be non-negated formulas) */
enum class RlvProperty : uint32_t
{
  NONE = 0,
  // is the atom relevant with true polarity?
  RLV_POS = 1,
  // is the atom relevant with false polarity?
  RLV_NEG = 2,
  // Has the atom been enqueued (sent as a theory atom to theory engine)?
  // Note polarity is agnostic, since we should never assert both true and
  // false. This holds only for theory literals.
  ENQUEUED = 4,
  // Has the atom been justified? This is used only for AND/OR/IMPLIES.
  JUSTIFIED = 8,
  // is the atom a top-level input or lemma with positive polarity?
  INPUT_POS = 16,
  // is the atom a top-level input or lemma with negative polarity?
  INPUT_NEG = 32,
  // has the atom been preregistered? True only for theory literals.
  PREREG = 64,
  // is the atom asserted with positive polarity?
  ASSERTED_POS = 128,
  // is the atom asserted with negative polarity?
  ASSERTED_NEG = 256,

  // temporary
  MARKED_PREREG = 512
};
/** Define operator lhs | rhs */
RlvProperty operator|(RlvProperty lhs, RlvProperty rhs);
/** Define operator lhs |= rhs */
RlvProperty& operator|=(RlvProperty& lhs, RlvProperty rhs);
/** Define operator lhs & rhs */
RlvProperty operator&(RlvProperty lhs, RlvProperty rhs);
/** Define operator lhs &= rhs */
RlvProperty& operator&=(RlvProperty& lhs, RlvProperty rhs);

class RlvInfo
{
 public:
  RlvInfo(context::Context* context);
  ~RlvInfo() {}
  /** The parents that we impact */
  context::CDList<TNode> d_parents;
  /** The polarity of the parent */
  context::CDList<bool> d_parentPol;
  /** The child polarity in the parent */
  context::CDList<bool> d_childPol;
  /** The properties */
  context::CDO<RlvProperty> d_rlvp;
  /** is relevant with polarity? */
  bool isRelevant(bool pol) const;
  /** is relevant with either polarity */
  bool isRelevant() const;
  /** set relevant with polarity */
  void setRelevant(bool pol);
  /** is enqueued? */
  bool isEnqueued() const;
  /** set enqueued? */
  void setEnqueued();
  /** is justified? */
  bool isJustified() const;
  /** set justified */
  void setJustified();
  /** is input? */
  bool isInput(bool& pol) const;
  /** set input */
  void setInput(bool pol);
  /** is preregistered? */
  bool isPreregistered() const;
  /** set preregistered */
  void setPreregistered();
  /** is asserted? */
  bool isAsserted(bool& pol) const;
  /** set asserted */
  void setAsserted(bool pol);
  /** is preregistered? */
  bool isMarkedPreregistered() const;
  /** set preregistered */
  void setMarkedPreregistered();
};

/**
 * SAT relevancy management
 */
class SatRelevancy : protected EnvObj
{
  typedef context::CDHashMap<TNode, std::shared_ptr<RlvInfo>> RlvMap;

 public:
  SatRelevancy(CDCLTSatSolverInterface* satSolver,
               TheoryEngine* theoryEngine,
               Env& env,
               CnfStream* cnfStream,
               options::SatRelevancyMode mode);

  ~SatRelevancy();
  /** presolve */
  void presolve(context::CDQueue<TNode>& queue);
  /**
   * Notify that lem is a new lemma, or an input formula. This adds new literals
   * that should be asserted at this time to theory engine, which are those
   * that were asserted but not relevant, but are now relevant based on this
   * lemma.
   *
   * Note the notification of lemmas is user-context dependent.
   */
  void notifyLemma(TNode lem, context::CDQueue<TNode>& queue);
  /**
   * Notify that lem is an activated skolem definition.
   *
   * The notification of lemmas is SAT-context dependent.
   */
  void notifyActivatedSkolemDefs(const std::vector<TNode>& lems,
                                 context::CDQueue<TNode>& queue);
  /**
   * Notify that the SAT solver has asserted literal l, which may be a theory
   * atom or a formula. Adds the literals that should be asserted to the theory
   * engine at this time to queue.
   *
   * For example, if l is not relevant, this may add nothing to queue. If l is
   * a formula whose children are atoms and have already been asserted, this
   * may trigger multiple literals to be added to queue.
   */
  void notifyAsserted(const SatLiteral& l, context::CDQueue<TNode>& queue);
  /** check */
  void check(theory::Theory::Effort effort, context::CDQueue<TNode>& queue);
  /** notify decision request */
  void notifyDecisionRequest(TNode n, context::CDQueue<TNode>& queue);
  /** Notify that atom n has been preregistered, i.e. assigned a SAT literal */
  void notifyPrereg(TNode n);
  /**
   * Similar as above, called for variables lemmas that are refreshed when
   * backtracking.
   */
  void notifyVarNotify(TNode n);
  // TEMPORARY
  void notifyPropagate(TNode n);

 private:
  /** Get or mk rlv info */
  RlvInfo* getOrMkRlvInfo(TNode n);
  /**
   * Set that n is relevant, add new theory literals to assert to TheoryEngine
   * in queue.
   */
  void setRelevant(TNode n,
                   bool pol,
                   context::CDQueue<TNode>* queue,
                   RlvInfo* ri = nullptr,
                   bool input = false);
  void setRelevantInternal(TNode n,
                           bool pol,
                           context::CDQueue<TNode>* queue,
                           RlvInfo* ri = nullptr,
                           bool input = false);
  /**
   * Set that atom has been assigned a value that makes a child of parent equal
   * to "pol", where parent is a term that was waiting for the value of atom.
   *
   * Adds relevant literals to be asserted to queue.
   *
   * Return true if the assignment to atom that led to this method being
   * called is relevant.
   */
  bool setAssertedChild(TNode atom,
                        bool pol,
                        TNode parent,
                        bool ppol,
                        context::CDQueue<TNode>& queue);
  /** has SAT value, if node has a value, return true and set value */
  bool hasSatValue(TNode node, bool& value);
  /**
   * Add parent to the relevant waiting parents of n.
   */
  void addParentRlvWait(TNode n, bool pol, TNode parentAtom, bool ppol);
  /** Ensure lemmas relevant */
  void ensureLemmasRelevant(context::CDQueue<TNode>* queue);
  /** If necessary, reregister the atom with the given relevancy info */
  void preregister(TNode atom, RlvInfo* ri);
  /** If necessary, enqueue atom with the given relevancy info */
  void enqueue(TNode atom,
               bool negated,
               RlvInfo* ri,
               context::CDQueue<TNode>* queue);
  /** Pointer to the SAT solver */
  CDCLTSatSolverInterface* d_satSolver;
  /** Pointer to theory engine */
  TheoryEngine* d_theoryEngine;
  /** pointer to the CNF stream */
  CnfStream* d_cnfStream;
  /**
   * The set of formulas that are asserted (user-context dependent).
   */
  context::CDList<TNode> d_inputs;
  /** the number of input formulas marked relevant */
  context::CDO<uint64_t> d_numInputs;
  /**
   * The relevancy waiting map, for each (non-negated) formula.
   */
  RlvMap d_rlvMap;
  // debugging
  bool d_isActiveTmp;
  context::CDO<uint64_t> d_numAsserts;
  context::CDO<uint64_t> d_numAssertsEnq;
  context::CDO<uint64_t> d_numAssertsRlv;
  context::CDO<uint64_t> d_numAssertsPrereg;
  /** The mode */
  options::SatRelevancyMode d_mode;
};

}  // namespace prop
}  // namespace cvc5

#endif /* CVC4__PROP__SAT_RELEVANCY_H */
