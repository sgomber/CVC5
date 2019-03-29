/*********************                                                        */
/*! \file inst_explain.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Instantiate explain utility
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_H
#define __CVC4__THEORY__QUANTIFIERS__INST_EXPLAIN_H

#include <map>
#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {


class InstExplain
{
public:
  std::vector< Node > d_insts;
};


class InstExplainDb
{
public:
  InstExplainDb();
  /** register explanations */
  void registerExplanation(Node ilem, Node n);
  /** get instantiation explain */
  InstExplain& getInstExplain( Node lit );
  /** explain */
  void explain( std::vector< Node >& exp );
private:
  /** common constants */
  Node d_false;
  /** map from literal to possible explanations */
  std::map< Node, InstExplain > d_lit_explains;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H */
