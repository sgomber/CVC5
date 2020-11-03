/*********************                                                        */
/*! \file subs.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simple substitution utility
 **/

#ifndef CVC4__EXPR__SUBS_H
#define CVC4__EXPR__SUBS_H

#include <vector>
#include "expr/node.h"

namespace CVC4 {

/**
 * Helper substitution class.
 */
class Subs
{
 public:
  bool empty() const;
  size_t size() const;
  bool contains(Node v) const;
  void add(Node v);
  void add(const std::vector<Node>& vs);
  void add(Node v, Node s);
  void add(const std::vector<Node>& vs, const std::vector<Node>& ss);
  void addEquality(Node eq);
  void append(Subs& s);
  void applyToRange(Subs& s);
  void rapplyToRange(Subs& s);
  Node apply(Node n) const;
  Node rapply(Node n) const;
  Node getEquality(size_t i) const;
  std::vector<Node> d_vars;
  std::vector<Node> d_subs;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__SUBS_H */
