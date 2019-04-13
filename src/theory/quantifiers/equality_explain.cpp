/*********************                                                        */
/*! \file equality_explain.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of instantiation explain database
 **/

#include "theory/quantifiers/equality_explain.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool EqExplainer::explainEe(eq::EqualityEngine* ee,
                            Node lit,
                            std::vector<TNode>& assumptions,
                            eq::EqProof* eqp)
{
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool pol = lit.getKind() != NOT;
  if (atom.getKind() == EQUAL)
  {
    if (ee->hasTerm(atom[0]) && ee->hasTerm(atom[1]))
    {
      if (pol)
      {
        if (!ee->areEqual(atom[0], atom[1]))
        {
          return false;
        }
      }
      else if (!ee->areDisequal(atom[0], atom[1], true))
      {
        return false;
      }
      Trace("eq-explain") << "explain eq" << atom << " " << pol << std::endl;
      ee->explainEquality(atom[0], atom[1], pol, assumptions, eqp);
      Trace("eq-explain") << "finished explain eq " << assumptions.size()
                          << std::endl;
      return true;
    }
  }
  else if (ee->hasTerm(atom))
  {
    Trace("eq-explain") << "explain pred" << atom << " " << pol << std::endl;
    ee->explainPredicate(atom, pol, assumptions, eqp);
    Trace("eq-explain") << "finished explain pred " << assumptions.size()
                        << std::endl;
    return true;
  }
  return false;
}

bool EqExplainerEe::explain(Node lit,
                            std::vector<TNode>& assumptions,
                            eq::EqProof* eqp)
{
  return explainEe(d_ee, lit, assumptions, eqp);
}

bool EqExplainerTe::explain(Node lit,
                            std::vector<TNode>& assumptions,
                            eq::EqProof* eqp)
{
  // currently we use a very simple heuristic here: we try to explain
  // using UF's equality engine only.
  Theory* t = d_te->theoryOf(THEORY_UF);
  if( t )
  {
    eq::EqualityEngine* ee = t->getEqualityEngine();
    if (ee)
    {
      return explainEe(ee, lit, assumptions, eqp);
    }
  }
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
