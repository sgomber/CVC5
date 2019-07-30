/*********************                                                        */
/*! \file proof_db.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof database
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__PROOF_DB__H
#define CVC4__THEORY__PROOF_DB__H

#include <map>
#include <vector>
#include "expr/node.h"
#include "theory/evaluator.h"
#include "theory/proof_db_pf.h"
#include "theory/proof_db_sc.h"
#include "theory/proof_db_term_process.h"
#include "theory/quantifiers/candidate_rewrite_filter.h"
#include "theory/quantifiers/term_canonize.h"

namespace CVC4 {
namespace theory {

/** ProofDb
 */
class ProofDb
{
 public:
  ProofDb();
  /**
   * Register rules
   */
  void registerRules(const std::map<Node, std::string>& rules);
  /** Exists rule? */
  bool existsRule(Node a, Node b, unsigned& index);
  bool existsRule(Node a, Node b);
  bool existsRule(Node p);
  /** Prove rule */
  bool proveRule(Node a, Node b);
  /** Notify */
  void notify(Node a, Node b, std::ostream& out);
  void notify(Node a, Node b);

 private:
  /** exists builtin rule */
  bool existsRuleInternal(Node a, Node b, unsigned& index, bool doRec);
  bool existsRuleInternal(Node p, unsigned& index, bool doRec);
  /** cache for exists rule */
  std::unordered_map<Node, bool, NodeHashFunction> d_erCache;
  /** common constants */
  Node d_true;
  Node d_false;
  /** currently allocating id */
  unsigned d_idCounter;
  /** map conclusions to proof ids */
  std::map<Node, std::vector<unsigned> > d_ids;
  /** map ids to proof rule information */
  std::map<unsigned, ProofDbRule> d_proofDbRule;
  /** map whether each condition has side conditions */
  std::unordered_set<Node, NodeHashFunction> d_hasSc;
  /** the term process utility */
  ProofDbTermProcess d_pdtp;
  /** the side condition utility */
  ProofDbScEval d_sceval;
  /** the evaluator utility */
  Evaluator d_eval;
  /** empty vector */
  std::vector<Node> d_emptyVec;
  /** the term canonization utility */
  quantifiers::TermCanonize d_canon;
  /** The match trie */
  quantifiers::MatchTrie d_mt;
  /** Notify class for the match trie */
  class ProofDbMatchTrieNotify : public quantifiers::NotifyMatch
  {
   public:
    ProofDbMatchTrieNotify(ProofDb& p) : d_parent(p) {}
    ProofDb& d_parent;

    bool notify(Node s,
                Node n,
                std::vector<Node>& vars,
                std::vector<Node>& subs) override
    {
      return d_parent.notifyMatch(s, n, vars, subs);
    }
  };
  ProofDbMatchTrieNotify d_notify;
  /**
   * Called during a call to d_mt.getMatches(s).
   * This call is called by the notify class for each term added to d_mt that
   * matches s under some substitution.
   */
  bool notifyMatch(Node s,
                   Node n,
                   std::vector<Node>& vars,
                   std::vector<Node>& subs);
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__PROOF_DB__H */
