/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #526
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
Solver solver;
solver.setOption("sets-ext", "true");
solver.setOption("produce-models", "true");
Sort s0 = solver.getBooleanSort();
Sort s1 = solver.mkSetSort(s0);
Term t2 = solver.mkConst(s1, "_x1");
Term t3 = solver.mkVar(s0, "_f3_0");
Op o4 = solver.mkOp(SET_CHOOSE);
Term t5 = solver.mkTerm(o4, {t2});
Sort s6 = solver.mkPredicateSort({s0});
Term t7 = solver.defineFun("_f3", {t3}, s0, t5);
Term t8 = solver.mkTerm(SET_CARD, {t2});
Sort s9 = t8.getSort();
solver.checkSat();
solver.blockModelValues({t7, t2, t2, t8});
Term t10 = solver.mkTerm(SET_COMPLEMENT, {t2});
Term t11 = solver.mkTerm(SET_SUBSET, {t10, t2});
solver.checkSat();
solver.checkSatAssuming({t11, t11, t11, t11, t11});

  return 0;
}
