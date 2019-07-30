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

ProofDb::ProofDb() : d_notify(*this)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_idCounter = static_cast<unsigned>(pf_rule_user);
}

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
    // make as expected matching: top symbol of all conditions is equality
    // this means (not p) becomes (= p false), p becomes (= p true)
    for (unsigned i = 0, nconds = conds.size(); i < nconds; i++)
    {
      if (conds[i].getKind() == NOT)
      {
        conds[i] = conds[i][0].eqNode(d_false);
      }
      else if (conds[i].getKind() != EQUAL)
      {
        conds[i] = conds[i].eqNode(d_true);
      }
    }
    // register with side condition utility
    for (const Node& c : conds)
    {
      if (d_sceval.registerSideCondition(c))
      {
        d_hasSc.insert(c);
      }
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

bool ProofDb::existsRuleInternal(Node a, Node b, unsigned& index, bool doRec)
{
  Node eq = a.eqNode(b);
  std::unordered_map<Node, unsigned, NodeHashFunction>::iterator it =
      d_erCache.find(eq);
  if (it != d_erCache.end())
  {
    if( it->second==pf_rule_invalid )
    {
      return false;
    }
    index = it->second;
    return true;
  }
  Trace("proof-db") << "ProofDb::existsRule " << a << "==" << b << "?"
                    << std::endl;
  if (a == b)
  {
    Trace("proof-db-debug") << "By reflexivity" << std::endl;
    // reflexivity
    index = pf_rule_refl;
    d_erCache[eq] = index;
    return true;
  }
  Node be = d_pdtp.toExternal(b);
  if (be.isConst())
  {
    Node ae = d_pdtp.toExternal(a);
    Trace("proof-db-debug") << "Check eval " << ae << std::endl;
    // evaluate it
    Node aev = d_eval.eval(ae, d_emptyVec, d_emptyVec);
    Trace("proof-db-eval") << "Eval [[" << ae << "]] = " << aev << std::endl;
    if (!aev.isNull())
    {
      Trace("proof-db-debug")
          << "Return evaluation " << (aev == be) << std::endl;
      // must check to see if it matches
      bool ret = (aev == be);
      index = ret ? pf_rule_eval : pf_rule_invalid;
      d_erCache[eq] = index;
      return ret;
    }
    Trace("proof-db-debug") << "Could not evaluate " << ae << std::endl;
  }
  Kind ak = a.getKind();
  Kind bk = b.getKind();
  if (ak == EQUAL && a[0] == a[1])
  {
    Trace("proof-db-debug") << "By equality reflexivity" << std::endl;
    // rewriting reflexive equality to true
    bool ret = (b.isConst() && b.getConst<bool>());
    index = ret ? pf_rule_eq_refl : pf_rule_invalid;
    d_erCache[eq] = index;
    return ret;
  }
  if (ak == EQUAL && bk == EQUAL)
  {
    if (a[0] == b[1] && b[0] == a[1])
    {
      Trace("proof-db-debug") << "By equality symmetry" << std::endl;
      // symmetry of equality
      index = pf_rule_eq_sym;
      d_erCache[eq] = index;
      return true;
    }
  }
  if (doRec)
  {
    // prevent infinite loops
    d_erCache[eq] = false;
    // is an instance of existing rule?
    if (!d_mt.getMatches(eq, &d_notify))
    {
      Assert( d_erCache.find(eq)!=d_erCache.end() );
      index = d_erCache[eq];
      Trace("proof-db-debug") << "By rule" << std::endl;
      return true;
    }
  }
  // congruence? TODO

  Trace("proof-db-debug") << "FAIL: no proof rule" << std::endl;
  index = pf_rule_invalid;
  d_erCache[eq] = index;
  return false;
}

bool ProofDb::existsRule(Node a, Node b, unsigned& index)
{
  if( existsRuleInternal(a, b, index, true) )
  {
    return true;
  }
  return false;
}

bool ProofDb::existsRule(Node a, Node b)
{
  unsigned index = 0;
  return existsRule(a, b, index);
}
bool ProofDb::existsRule(Node p)
{
  if (p.getKind() == EQUAL)
  {
    return existsRule(p[0], p[1]);
  }
  return existsRule(p, d_true);
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
  // out << "(trusted-debug (= " << ai << " " << bi << "))" << std::endl;
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
#ifdef CVC4_ASSERTIONS
  Assert(vars.size() == subs.size());
  for (unsigned i = 0, size = vars.size(); i < size; i++)
  {
    Assert(vars[i].getType().isComparableTo(subs[i].getType()));
  }
  Assert(d_ids.find(n) != d_ids.end());
#endif
  // check each rule instance
  for (unsigned ruleId : d_ids[n])
  {
    Assert(d_proofDbRule.find(ruleId) != d_proofDbRule.end());
    // get the proof rule
    ProofDbRule& pr = d_proofDbRule[ruleId];
    // does the side condition hold?
    bool condSuccess = true;
    Trace("proof-db") << "Check rule " << pr.d_name << std::endl;
    for (const Node& cond : pr.d_cond)
    {
      // check whether condition holds?
      condSuccess = false;
      Node sc =
          cond.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      Trace("proof-db-infer-sc") << "Check condition: " << sc << std::endl;
      // if i have side conditions, first evaluate
      if (d_hasSc.find(cond) != d_hasSc.end())
      {
        Trace("proof-db-infer-sc")
            << "..." << pr.d_name << " eliminate side conditions in " << sc
            << std::endl;
        sc = d_sceval.evaluate(sc);
        Trace("proof-db-infer-sc")
            << "..." << pr.d_name << " returned " << sc << std::endl;
        condSuccess = existsRule(sc);
      }
      else
      {
        Assert(sc.getType().isBoolean());
        // now check whether it is true
        condSuccess = existsRule(sc);
      }
      if (!condSuccess)
      {
        if (Trace.isOn("proof-db"))
        {
          // see if it was a provable fact that we failed to show
          // cannot invoke rewriter here
          // Node scr = Rewriter::rewrite(sc);
          // if( scr.isConst() && scr.getConst<bool>() )
          //{
          Trace("proof-db")
              << "required: " << sc << " for " << pr.d_name << std::endl;
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
      d_erCache[s] = ruleId;
      return false;
    }
  }

  return true;
}

}  // namespace theory
}  // namespace CVC4
