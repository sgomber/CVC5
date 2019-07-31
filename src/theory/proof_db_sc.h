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

#ifndef CVC4__THEORY__PROOF_DB_SC__H
#define CVC4__THEORY__PROOF_DB_SC__H

#include <string>
#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace theory {

class ProofDbScEval
{
 public:
  ProofDbScEval();
  /** returns true if there is at least one side condition in sc */
  bool registerSideCondition(Node sc);
  Node evaluate(Node n);

  bool isSideConditionOp(Node op) const;
  
  static Node purifySideConditions(Node n, std::vector< Node >& scs);
 private:
  enum SideConditionId
  {
    sc_INVALID,
    sc_flatten_string,
    sc_flatten_regexp,
    sc_sort_regexp,
    sc_re_loop_elim,
    sc_arith_norm_term,
    sc_arith_norm_term_abs,
    sc_sort_bool,
    sc_LAST,
  };
  std::map<std::string, SideConditionId> d_symTable;
  std::map<Node, SideConditionId> d_opTable;
  /** build operator table
   *
   *
   * Returns true if there is at least one side condition in n
   */
  bool buildOperatorTable(Node n);

  Node evaluateApp(Node op, const std::vector<Node>& args);

  /** common constants */
  Node d_zero;
  Node d_one;
  Node d_negOne;
  Node d_true;
  Node d_false;
  Node d_reEmp;
  Node d_reAll;

  /** specific side conditions */
  Node flatten_string(Node n);
  Node flatten_regexp(Node n);
  Node sort_regexp(Node n);
  Node re_loop_elim(Node n);
  Node arith_norm_term(Node n);
  Node arith_norm_term_abs(Node n);
  Node sort_bool(Node n);

  /** Helpers */
  Node h_flattenCollect(Kind k, Node n, Node acc);
  void h_termToVec(Kind k, Node n, std::vector<Node>& terms);
  Node h_vecToTerm(Kind k, const std::vector<Node>& terms);
  void h_termToMsum(Node n, std::map<Node, Node>& msum);
  Node h_msumToTerm(std::map<Node, Node>& msum, bool posLeadingCoeff = false);
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__PROOF_DB__H */
