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
#include <unordered_map>
#include "expr/node.h"
#include "theory/quantifiers/candidate_rewrite_filter.h"
#include "theory/quantifiers/term_canonize.h"

namespace CVC4 {
namespace theory {

/** 
  * The AST structure of terms in the proof checker and in CVC4 is different.
  * This class converts between the two expected AST structures. These
  * differences include:
  * (1) CVC4 has n-ary associative operators; the proof checker assumes binary
  * applications only,
  * (2) CVC4 has (word) string literals; the proof checker assumes these are
  * concatenations of constants, e.g. "ABC" is (str.++ "A" (str.++ "B" "C")).
  * 
  */
class ProofDbTermProcess
{
public:
  /** convert to internal 
   * 
   * This converts the node n to the internal shape that it would be in
   * the proof checker. This means that n-ary applications are converted
   * to (left-associative) chains.   
   */
  Node toInternal(Node n);
  /** convert to external
   * 
   * Inverse of the above translation
   */
  Node toExternal(Node n);
  /** is associative */
  static bool isAssociativeNary(Kind k);
private:
  /** Map from nodes to their internal representation */
  std::unordered_map< Node, Node, NodeHashFunction > d_internal;
  std::unordered_map< Node, Node, NodeHashFunction > d_external;
};

class ProofDbRule
{
 public:
  std::string d_name;
  Node d_cond;
  Node d_eq;

  void init(const std::string& name, Node cond, Node eq);
};

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
  /** Prove rule */
  bool proveRule(Node a, Node b);
  /** Notify */
  void notify(Node a, Node b, std::ostream& out);
  void notify(Node a, Node b);

 private:
  /** currently allocating id */
  unsigned d_idCounter;
  /** map conclusions to proof ids */
  std::map<Node, std::vector<unsigned> > d_ids;
  /** map ids to proof rule information */
  std::map<unsigned, ProofDbRule> d_proofDbRule;
  /** the term process utility */
  ProofDbTermProcess d_pdtp;

  quantifiers::TermCanonize d_canon;
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
  quantifiers::MatchTrie d_mt;
  bool notifyMatch(Node s,
                   Node n,
                   std::vector<Node>& vars,
                   std::vector<Node>& subs);
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__PROOF_DB__H */
