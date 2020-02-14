/*********************                                                        */
/*! \file arith_msum_nl.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief arith_msum
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__MSUM_NL_H
#define CVC4__THEORY__ARITH__MSUM_NL_H

#include <map>

#include "expr/node.h"

namespace CVC4 {
namespace theory {

/** Arithmetic utilities regarding monomial sums.
 *
 * Note the following terminology:
 *
 *   We say Node c is a {monomial constant} (or m-constant) if either:
 *   (a) c is a constant Rational, or
 *   (b) c is null.
 *
 *   We say Node v is a {monomial variable} (or m-variable) if either:
 *   (a) v.getType().isReal() and v is not a constant, or
 *   (b) v is null.
 *
 *   For m-constant or m-variable t, we write [t] to denote 1 if t.isNull() and
 *   t otherwise.
 *
 *   A monomial m is a pair ( mvariable, mconstant ) of the form ( v, c ), which
 *   is interpreted as [c]*[v].
 *
 *   A {monmoial sum} msum is represented by a std::map< Node, Node > having
 *   key-value pairs of the form ( mvariable, mconstant ).
 *   It is interpreted as:
 *   [msum] = sum_{( v, c ) \in msum } [c]*[v]
 *   It is critical that this map is ordered so that operations like adding
 *   two monomial sums can be done efficiently. The ordering itself is not
 *   important, and currently corresponds to the default ordering on Nodes.
 *
 * The following has utilities involving monmoial sums.
 *
 */
class ArithMSumNl
{
 public:
  /** get monomial
   *
   * If n = n[0]*n[1] where n[0] is constant and n[1] is not,
   * this function returns true, sets c to n[0] and v to n[1].
   */
  static bool getMonomial(Node var, Node n, Node& c);

  /** get monomial accumulate
   *
   * If this function returns true, it adds the ( m-constant, m-variable )
   * pair corresponding to the monomial representation of n to the
   * monomial sum msum.
   *
   * This function returns false if the m-variable of n is already
   * present in n.
   */
  static bool getMonomialAcc(Node var, Node n, Node& coeff);


  /** solve equality lit for variable
   *
   * If return value ret is non-null, then:
   *    v = ret is equivalent to lit.
   *
   * This function may return false if lit does not contain v,
   * or if lit is an integer equality with a coefficent on v,
   * e.g. 3*v = 7.
   */
  static Node solve(Node poly, Node var);
  static Node solveEqualityFor(Node lit, Node var);
};

} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__ARITH__MSUM_NL_H */
