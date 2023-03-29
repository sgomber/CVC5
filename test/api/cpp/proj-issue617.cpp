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
 * Test for project issue #617
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setLogic("QF_NRA");
  solver.setOption("check-models", "true");
  Sort s0 = solver.getRealSort();
  Term t1 = solver.mkConst(s0, "_x0");
  Term t2 = solver.mkConst(s0, "_x1");
  Term t3 = solver.mkConst(s0, "_x2");
  Term t4 = solver.mkReal("6790089/71203");
  Term t5 = solver.mkReal("354131059765066077956502439364245754373025");
  Term t6 = solver.mkConst(s0, "_x3");
  Term t7 = solver.mkReal("640/79251919");
  Term t8 = solver.mkTerm(GT, {t2, t7});
  Sort s9 = t8.getSort();
  Op o10 = solver.mkOp(GT);
  Term t11 = solver.mkTerm(o10, {t2, t1});
  Op o12 = solver.mkOp(IMPLIES);
  Term t13 = solver.mkTerm(o12, {t8, t11, t8});
  Op o14 = solver.mkOp(MULT);
  Term t15 = solver.mkTerm(o14, {t1, t5, t6});
  Op o16 = solver.mkOp(NOT);
  Term t17 = solver.mkTerm(o16, {t13});
  solver.assertFormula(t13);
  Op o18 = solver.mkOp(DIVISION);
  Term t19 = solver.mkTerm(o18, {t15, t3});
  Op o20 = solver.mkOp(NEG);
  Term t21 = solver.mkTerm(o20, {t6});
  Op o22 = solver.mkOp(NEG);
  Term t23 = solver.mkTerm(o20, {t21});
  Op o24 = solver.mkOp(ITE);
  Term t25 = solver.mkTerm(o24, {t17, t13, t17});
  Term t26 = solver.mkTerm(NEG, {t23});
  Op o27 = solver.mkOp(ITE);
  Term t28 = t11.iteTerm(t26, t26);
  Op o29 = solver.mkOp(AND);
  Term t30 = t25.andTerm(t25);
  Term t31 = solver.mkTerm(NEG, {t28});
  Op o32 = solver.mkOp(ITE);
  Term t33 = solver.mkTerm(o24, {t30, t2, t31});
  Term t34 = solver.mkTerm(DIVISION, {t33, t31, t7});
  Op o35 = solver.mkOp(DIVISION);
  Term t36 = solver.mkTerm(o18, {t26, t6, t4, t34, t31});
  Term t37 = solver.mkTerm(NEG, {t36});
  Op o38 = solver.mkOp(GEQ);
  Term t39 = solver.mkTerm(o38, {t2, t2});
  Op o40 = solver.mkOp(ITE);
  Term t41 = solver.mkTerm(o24, {t39, t37, t2});
  Op o42 = solver.mkOp(LEQ);
  Term t43 = solver.mkTerm(o42, {t41, t31, t3});
  Op o44 = solver.mkOp(LEQ);
  Term t45 = solver.mkTerm(o42, {t2, t37, t19});
  Term t46 = solver.mkTerm(GT, {t1, t6});
  Term t47 = solver.mkTerm(LT, {t5, t23});
  Op o48 = solver.mkOp(ITE);
  Term t49 = solver.mkTerm(o24, {t46, t34, t31});
  Op o50 = solver.mkOp(GEQ);
  Term t51 = solver.mkTerm(o38, {t49, t21, t36});
  Term t52 = solver.mkTerm(XOR, {t47, t45});
  Op o53 = solver.mkOp(XOR);
  Term t54 = solver.mkTerm(o53, {t51, t52});
  solver.assertFormula(t43);
  solver.assertFormula(t54);
  solver.checkSat();

  return 0;
}
