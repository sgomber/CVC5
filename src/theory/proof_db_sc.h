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
  void registerSideCondition(Node sc);
  Node evaluate(Node n);

  bool isSideConditionOp( Node op ) const;
 private:
  enum SideConditionId
  {
    sc_INVALID,
    sc_flatten,
  };
  std::map< std::string, SideConditionId > d_symTable;
  std::map< Node, SideConditionId > d_opTable;
  /** build operator table 
   */
  void buildOperatorTable( Node n );
  
  Node evaluateApp(Node op, const std::vector< Node >& args);

  /** specific side conditions */
  Node flatten(Node n);
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__PROOF_DB__H */
