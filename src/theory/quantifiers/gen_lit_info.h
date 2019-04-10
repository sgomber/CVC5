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

/** generalized literal information
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
class GLitInfo
{
 public:
  GLitInfo() : d_iei(nullptr), d_upgTriv(true) {}
  /** the instantiation lemma that this generalization is based on */
  InstExplainInst* d_iei;
  /** matching constraints regarding "how general" the literal is, initially
   * empty. */
  std::map<TNode, Node> d_subs_modify;
  /** required assumptions */
  std::vector<Node> d_assumptions;
  /** required conclusions, which are themselves generalized literals */
  std::map<Node, std::map<Node, GLitInfo> > d_conclusions;
  /** initialize this information
   *
   * This sets d_iei to iei and clears the above vectors.
   */
  void initialize(InstExplainInst* iei);
  /** initialize to the result of merging the generalizations of a and b
   *
   * It should be the case that ( a * SUBS(ga) ) = ( b * SUBS(gb) ).
   *
   * For example:
   */
  // bool initialize(TNode a, const GLitInfo& ga, TNode b, const GLitInfo& gb);

  // bool merge(TNode a, TNode b, const GLitInfo& gb, bool allowBind = true);
  /** set conclusion
   */
  void setConclusion(Node pl, Node opl);
  void setOpenConclusion(Node pl);
  /**
   * Check whether ( b * SUBS(gb) ) is a generalization of a.
   */
  bool checkCompatible(TNode a, TNode b, const GLitInfo& gb);
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

  void debugPrint(const char* c, unsigned tb = 0) const;

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

  /** get the UPG
   */
  void processUPG(InstExplainDb& ied,
                  Node currConc,
                  std::vector<Node>& assumptions,
                  std::vector<Node>& lemmas,
                  std::map<Node, Node>& subsumptions) const;

  /** get upg lit */
  Node getUPGLit() const { return d_upgLit; }
  /** is upg trivial */
  bool isUPGTrivial() const { return d_upgTriv; }
 private:
  bool mergeInternal(
      TNode a, TNode b, const GLitInfo& gb, bool doMerge, bool allowBind);
  /** indent tb tabulations on trace c */
  void indent(const char* c, unsigned tb) const;
  /** upg literal */
  Node d_upgLit;
  /** is upg literal non-trivial? */
  bool d_upgTriv;
  
  void setOpenConclusionInternal(Node opl);
  void notifyOpenConclusion(Node opl, bool isTriv);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__GEN_LIT_INFO_H */
