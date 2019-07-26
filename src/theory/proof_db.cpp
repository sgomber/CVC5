/*********************                                                        */
/*! \file proof_db.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of Proof db.
 **/

#include "theory/proof_db.h"
#include "theory/theory.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

ProofDb::ProofDb() : d_idCounter(1), d_notify(*this) {}

void ProofDb::registerRules(const std::map<Node, std::string>& rules)
{
  // add each of the rules to the database
  for (const std::pair<const Node, std::string>& rr : rules)
  {
    Node r = rr.first;
    // convert to internal
    Node ri = d_pdtp.toInternal(r);
    AlwaysAssert(r.getKind() == IMPLIES);

    // must canonize
    Trace("proof-db") << "Add rule " << rr.second << ": " << r[1] << std::endl;
    Node cr = d_canon.getCanonicalTerm(ri, false, false);

    Node cond = cr[0];
    std::vector<Node> conds;
    if (cond.getKind() == AND)
    {
      for (const Node& c : cond)
      {
        // should flatten in proof inference listing
        Assert(c.getKind() != AND);
        conds.push_back(c);
      }
    }
    else if (!cond.isConst())
    {
      conds.push_back(cond);
    }
    else if (!cond.getConst<bool>())
    {
      // skip those with false condition
      continue;
    }

    // register with side condition utility
    for (const Node& c : conds)
    {
      d_sceval.registerSideCondition(c);
    }

    Node eq = cr[1];

    // add to discrimination tree
    Trace("proof-db-debug") << "Add (Canonical) rule " << eq << std::endl;
    d_mt.addTerm(eq);

    // remember rules
    d_ids[eq].push_back(d_idCounter);
    d_proofDbRule[d_idCounter].init(rr.second, conds, eq);
    d_idCounter++;
  }
}

bool ProofDb::existsRule(Node a, Node b, unsigned& index)
{
  Trace("proof-db-debug") << "ProofDb::existsRule " << a << "==" << b << std::endl;
  if (a == b)
  {
    // reflexivity
    return true;
  }
  Node be = d_pdtp.toExternal(b);
  if (be.isConst())
  {
    Node ae = d_pdtp.toExternal(a);
    Trace("proof-db-debug") << "Check eval " << ae << std::endl;
    // evaluate it
    Node aev = d_eval.eval(ae,d_emptyVec,d_emptyVec);
    if( !aev.isNull() )
    {
      Trace("proof-db-debug") << "Return evaluation " << (aev==be) << std::endl;
      // must check to see if it matches
      return aev==be;
    }
    Trace("proof-db-debug") << "Could not evaluate " << ae << std::endl;
  }
  Kind ak = a.getKind();
  Kind bk = b.getKind();
  if (ak == EQUAL && a[0] == a[1])
  {
    Trace("proof-db-debug") << "By equality reflexivity" << std::endl;
    // rewriting reflexive equality to true
    return b.isConst() && b.getConst<bool>();
  }
  if (ak == EQUAL && bk == EQUAL)
  {
    if (a[0] == b[1] && b[0] == a[1])
    {
      Trace("proof-db-debug") << "By equality symmetry" << std::endl;
      // symmetry of equality
      return true;
    }
  }
  TheoryId at = Theory::theoryOf(a);
  if (at == THEORY_ARITH)
  {
    if( a.getType().isReal() )
    {
      // normalization?
      Trace("proof-db-debug") << "By arith normalization?" << std::endl;
      return true;
    }
  }
  if (at == THEORY_BOOL)
  {
    // normalization? ignore for now
    Trace("proof-db-debug") << "By Bool normalization?" << std::endl;
    return true;
  }
  Node eq = a.eqNode(b);
  // is an instance of existing rule?
  if (!d_mt.getMatches(eq, &d_notify))
  {
    Trace("proof-db-debug") << "By rule" << std::endl;
    return true;
  }
  Trace("proof-db-debug") << "FAIL: no proof rule" << std::endl;
  return false;
}

bool ProofDb::existsRule(Node a, Node b)
{
  unsigned index = 0;
  return existsRule(a, b, index);
}

bool ProofDb::proveRule(Node a, Node b)
{
  Assert(!existsRule(a, b));
  // trusted reduction, try to prove

  return false;
}

void ProofDb::notify(Node a, Node b)
{
  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
  notify(a, b, *nodeManagerOptions.getOut());
}

void ProofDb::notify(Node a, Node b, std::ostream& out)
{
  Trace("proof-db-debug") << "Notify " << a << " " << b << std::endl;
  // must convert to internal
  Node ai = d_pdtp.toInternal(a);
  Node bi = d_pdtp.toInternal(b);
  Trace("proof-db-debug") << "Notify internal " << ai << " " << bi << std::endl;
  if (existsRule(ai, bi))
  {
    // already exists
    return;
  }
  out << "(trusted (= " << a << " " << b << "))" << std::endl;
}

bool ProofDb::notifyMatch(Node s,
                          Node n,
                          std::vector<Node>& vars,
                          std::vector<Node>& subs)
{
  Trace("proof-db-infer-debug")
      << "ProofDb::notifyMatch: " << s
      << " is instance of existing rule:" << std::endl;
  Trace("proof-db-infer-debug") << "  " << n << std::endl;
  Trace("proof-db-infer-debug")
      << "  substitution: " << vars << " -> " << subs << std::endl;
  Assert(d_ids.find(n) != d_ids.end());
  // check each rule instance
  for (unsigned ruleId : d_ids[n])
  {
    Assert(d_proofDbRule.find(ruleId) != d_proofDbRule.end());
    // get the proof rule
    ProofDbRule& pr = d_proofDbRule[ruleId];
    // does the side condition hold?
    bool condSuccess = true;
    Trace("proof-db-rules") << "Check rule " << pr.d_name << std::endl;
    for (const Node& cond : pr.d_cond)
    {
      // check whether condition holds?
      condSuccess = false;
      Node sc =
          cond.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      Trace("proof-db-infer-sc") << "Check condition: " << sc << std::endl;
      Kind sck = sc.getKind();
      if (sck == EQUAL)
      {
        if (sc[0].getKind() == APPLY_UF)
        {
          // a computational side condition, call sc utility
          Node res = d_sceval.evaluate(sc[0]);
          Trace("proof-db-infer-sc") << "... returned " << res << std::endl;
          Trace("proof-db-infer-sc") << "... expected " << sc[1] << std::endl;
          condSuccess = (res == sc[1]);
        }
        else if( existsRule(sc[0],sc[1]) )
        {
          // recursed, found
          condSuccess = true;
        }
      }
      if (!condSuccess)
      {
        if( Trace.isOn("proof-db-req") )
        {
          // see if it was a provable fact that we failed to show
          // cannot invoke rewriter here
          //Node scr = Rewriter::rewrite(sc);
          //if( scr.isConst() && scr.getConst<bool>() )
          //{
          Trace("proof-db-req") << "required: " << sc << " for " << pr.d_name << std::endl;
          //}
        }
        break;
      }
    }
    if (condSuccess)
    {
      // successfully found instance of rule
      if (Trace.isOn("proof-db-infer"))
      {
        Node se = d_pdtp.toExternal(s);
        Trace("proof-db-infer")
            << "INFER " << se << " by " << pr.d_name << std::endl;
      }
      return false;
    }
  }

  return true;
}

}  // namespace theory
}  // namespace CVC4
