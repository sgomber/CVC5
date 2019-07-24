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
#include "expr/node.h"

namespace CVC4 {
namespace theory {

class ProofDbRule
{
public:
  std::string d_name;
  Node d_cond;
  Node d_eq;
};
  
/** ProofDb
 */
class ProofDb
{
 public:
  /**
   * Register rules
   */
  void registerRules(const std::map< Node, std::string >& rules);
  /** Exists rule? */
  bool existsRule( Node eq, unsigned& index );
  /** Prove rule */
  bool proveRule( Node eq );
  /** Notify */
  bool notify( Node a, Node b );
private:
  // TODO
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__PROOF_DB__H */
