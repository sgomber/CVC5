/*********************                                                        */
/*! \file gen_lit_info.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Generalized literal info
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__GEN_LIT_INFO_H
#define __CVC4__THEORY__QUANTIFIERS__GEN_LIT_INFO_H

#include <map>
#include <vector>
#include "expr/node.h"
#include "theory/quantifiers/inst_explain.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class InstExplainDb;

class IexOutput
{
 public:
  IexOutput(InstExplainDb& i) : d_iexd(i) {}
  /** report conclusion
   */
  Node reportConclusion(InstExplainInst* iei,
                        const std::vector<Node>& assumps,
                        const std::vector<Node>& concs,
                        bool doGenCInst = true);
  /** is the content of this output empty? */
  bool empty() const;
  /** reference to the explanation database. */
  InstExplainDb& d_iexd;
  /** the lemmas generated using this output */
  std::vector<Node> d_lemmas;
  /** the subsumptions from using this output */
  std::map<Node, Node> d_subsumed_by;
};

/** instantiation explain proof
 *
 * This stores the state of a generalized literal. This consists of three parts:
 * (1) A substitution,
 * (2) A set of assumptions,
 * (3) A set of conclusions.
 *
 * The meaning of this information is dependent upon the pointer d_iei,
 * which stores information pertaining to an instantiation lemma. Let Q
 * be the quantified formula of this instantation lemma. For an instance of this
 * class G, we write
 *   SUBS_GROUND(G)
 * to denote the substitution associated with the instantiation lemma of
 * G.d_iei.
 *
 * Notice a literal itself is not stored in this class. Instead, this class
 * is a way of interpretting a class of literals whose free variables are a
 * subset of the variables bound by the quantified formula Q.
 *
 * The substitution is represented using the pointer d_iei plus the map
 * d_subs_modify. Let:
 *    SUBS(G) = { x -> d_subs_modify[x] | x in domain(d_subs_modify) }
 *
 * A literal L may be interpreted as a generalized literal via an instance of
 * this class G in the following way. An instance of G says that the following
 * entailment holds:
 *   assumptions |= forall x. ( L * SUBS(G) ) V conclusions
 * where x are the free variables of L * SUBS(G), conclusions.
 */
class IexProof
{
 public:
  IexProof() : d_iei(nullptr), d_upgTriv(true) {}
  /** is empty */
  bool empty() const;
  /** the instantiation lemma that this generalization is based on */
  InstExplainInst* d_iei;
  /** matching constraints regarding "how general" the literal is, initially
   * empty. */
  std::map<TNode, Node> d_subs_modify;
  /** required assumptions */
  std::vector<Node> d_assumptions;
  /** required conclusions, which are themselves generalized literals */
  std::map<Node, std::map<Node, IexProof> > d_conclusions;
  /** initialize this information
   *
   * This sets d_iei to iei and clears everything else.
   */
  void initialize(InstExplainInst* iei);
  /** set conclusion
   *
   * This indicates that we have decided to justify the premise (pl/opl) with
   * the proof stored at d_conclusions[pl][opl].
   *
   * There are two cases:
   * (1) The proof d_conclusions[pl][opl] is purely general. In this case,
   * we take the assumptions from this proof and remove it from d_conclusions,
   * i.e. we compress its proof,
   * (2) The proof d_conclusions[pl][opl] contains a UPG.
   *   (A) If proofs of all premises registered by previous calls have been
   *   purely general, then we leave d_conclusions[pl][opl] unchanged, and set
   *   the UPG literal (d_upgLit/d_upgOLit) to (pl/opl),
   *   (B) If we already have a propagating generalization in the proof of
   *   another premise (pl'/opl'), then we discard the propagating
   *   generalizations in both proofs and make both (pl/opl) and (pl'/opl')
   *   to be open leaves,
   *   (C) If we already have open leaves (pl_1/opl_1) ... (pl_n/opl_n), then
   *   we discard the UPG from the proof of d_conclusions[pl][opl] and (pl/opl)
   *   is made an open leaf.
   */
  void setConclusion(Node pl, Node opl);
  /**
   * This indicates that we cannot justify the premise (pl/opl). Hence it
   * becomes an open leaf.
   *
   * If we contain a proof of a premise (pl'/opl') that has a UPG, it is
   * discarded and (pl'/opl') becomes an open leaf.
   */
  void setOpenConclusion(Node pl, Node opl);
  /**
   * Check whether ( b * SUBS(gb) ) is a generalization of a.
   */
  bool checkCompatible(TNode a, TNode b, const IexProof& gb);
  /**
   * Check whether b is a generalization of a.
   */
  bool checkCompatible(TNode a, TNode b);

  bool drop(TNode b);

  /** get score
   *
   * This is a heuristic value, the smaller the value, the more general it is.
   */
  unsigned getScore() const;

  void debugPrint(const char* c, unsigned tb = 0, bool rec = true) const;

  bool isPurelyGeneral() const;
  Node getAssumptions() const;
  /** is the proof of lit open? */
  bool isOpen(Node lit) const;
  bool hasUPG() const;
  /** get the UPG
   */
  InstExplainInst* getUPG(std::vector<Node>& concs,
                          Node& quant,
                          std::vector<Node>& assumptions) const;

  /** get upg lit */
  Node getUPGLit() const { return d_upgLit; }
  /** is upg trivial */
  bool isUPGTrivial() const { return d_upgTriv; }

  /** process UPG
   *
   * This adds lemmas to FIXME
   */
  void processUPG(IexOutput& iout, Node currConc) const;

 private:
  bool mergeInternal(
      TNode a, TNode b, const IexProof& gb, bool doMerge, bool allowBind);
  /** indent tb tabulations on trace c */
  void indent(const char* c, unsigned tb) const;
  /**
   * A ground/generalized literals whose proof contains a UPG, or a premise
   * that is part of the UPG itself.
   */
  Node d_upgLit;
  Node d_upgOLit;
  /** Are the above literals part of the UPG itself? */
  bool d_upgTriv;
  /** set open conclusion internal
   *
   * This makes pl/opl an open leaf of this proof.
   */
  void setOpenConclusionInternal(Node pl, Node opl);
  /** notify open conclusion
   *
   * Notify that (pl/opl) is justified by a proof that is not purely general.
   * The flag isTriv is true if (pl/opl) is an open leaf.
   *
   * This call ensures that this proof has a unique propagating generalization
   * by the following steps:
   *
   * 1. (Undo previous UPG if one exists)
   * If d_upgTriv is false, this indicates that a proof of the premise
   * (d_upgLit/d_upgOLit) contains a propagating generalization. We discard
   * its generalization.
   *
   * 2. (Set UPG if available)
   * If d_upgLit is null, then we set the UPG literal to pl/opl.
   *
   * 3. (Undo UPG in current literal if UPG is not available)
   * If pl/opl has a non-trivial UPG, it must be discarded if there was already
   * a UPG literal.
   */
  void notifyOpenConclusion(Node pl, Node opl, bool isTriv);
  /** process UPG internal
   *
   * This adds
   */
  void processUPGInternal(IexOutput& iout,
                          Node currConc,
                          std::vector<Node>& assumptions) const;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__GEN_LIT_INFO_H */
