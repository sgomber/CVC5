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

ProofDb::ProofDb() : d_notify(*this), d_proofPrinting(false)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_idCounter = static_cast<unsigned>(pf_rule_user);
}

void ProofDb::registerRules(const std::map<Node, std::string>& rules)
{
  NodeManager* nm = NodeManager::currentNM();
  // add each of the rules to the database
  for (const std::pair<const Node, std::string>& rr : rules)
  {
    Node r = rr.first;
    AlwaysAssert(r.getKind() == IMPLIES);
    // we canonize left-to-right, hence we should traverse in the opposite
    // order, since we index based on conclusion
    Node tmp = nm->mkNode(IMPLIES, r[1], r[0]);
    // convert to internal
    Node tmpi = d_pdtp.toInternal(tmp);

    // must canonize
    Trace("proof-db") << "Add rule " << rr.second << ": " << r[1] << std::endl;
    Node cr = d_canon.getCanonicalTerm(tmpi, false, false);

    Node cond = cr[1];
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

    Node eq = cr[0];

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
    if (it->second == pf_rule_invalid)
    {
      Assert(!d_proofPrinting);
      return false;
    }
    else if (!d_proofPrinting)
    {
      index = it->second;
      return true;
    }
  }
  else
  {
    // should have already computed the proof
    Assert(!d_proofPrinting);
  }
  Trace("proof-db") << "ProofDb::existsRule " << a << "==" << b << "?"
                    << std::endl;
  if (a == b)
  {
    Trace("proof-db-debug") << "By reflexivity" << std::endl;
    // reflexivity
    index = pf_rule_refl;
    if (d_proofPrinting)
    {
      d_pfStream << "(refl " << a << ")";
      return true;
    }
    d_erCache[eq] = index;
    return true;
  }
  Node ae = d_pdtp.toExternal(a);
  Node be = d_pdtp.toExternal(b);
  Trace("proof-db-debug") << "Check eval " << ae << std::endl;
  // evaluate it
  Node bev = d_eval.eval(be, d_emptyVec, d_emptyVec);
  Node aev = d_eval.eval(ae, d_emptyVec, d_emptyVec);
  Trace("proof-db-eval") << "Eval [[" << ae << "]] = " << aev << std::endl;
  Trace("proof-db-eval") << "Eval [[" << be << "]] = " << bev << std::endl;
  if (!aev.isNull() && !bev.isNull())
  {
    Trace("proof-db-debug")
        << "Return evaluation " << (aev == bev) << std::endl;
    if (d_proofPrinting)
    {
      d_pfStream << "(eval " << a << " " << b << ")";
      return true;
    }
    // must check to see if it matches
    bool ret = (aev == bev);
    index = ret ? pf_rule_eval : pf_rule_invalid;
    d_erCache[eq] = index;
    return ret;
  }
  Trace("proof-db-debug") << "Could not evaluate " << ae << std::endl;
  Kind ak = a.getKind();
  Kind bk = b.getKind();
  if (ak == EQUAL && a[0] == a[1])
  {
    Trace("proof-db-debug") << "By equality reflexivity" << std::endl;
    if (d_proofPrinting)
    {
      d_pfStream << "(eq-refl " << a[0] << ")";
      return true;
    }
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
      if (d_proofPrinting)
      {
        d_pfStream << "(eq-sym " << a[0] << " " << a[1] << ")";
        return true;
      }
      d_erCache[eq] = index;
      return true;
    }
  }
  if (doRec)
  {
    // prevent infinite loops
    if (!d_proofPrinting)
    {
      d_erCache[eq] = 0;
    }
    // is an instance of existing rule?
    if (!d_mt.getMatches(eq, &d_notify))
    {
      Trace("proof-db-debug") << "By rule" << std::endl;
      Assert(d_erCache.find(eq) != d_erCache.end());
      if (!d_proofPrinting)
      {
        index = d_erCache[eq];
      }
      return true;
    }
  }
  // congruence? TODO
  Assert(!d_proofPrinting);
  Trace("proof-db-debug") << "FAIL: no proof rule" << std::endl;
  index = pf_rule_invalid;
  d_erCache[eq] = index;
  return false;
}

bool ProofDb::existsRule(Node a, Node b, unsigned& index)
{
  if (existsRuleInternal(a, b, index, true))
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

void ProofDb::notify(Node a, Node b)
{
  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
  notify(a, b, *nodeManagerOptions.getOut());
}

void ProofDb::notify(Node a, Node b, std::ostream& out)
{
  AlwaysAssert(!d_proofPrinting);
  Trace("proof-db-debug") << "Notify " << a << " " << b << std::endl;
  // must convert to internal
  Node ai = d_pdtp.toInternal(a);
  Node bi = d_pdtp.toInternal(b);
  Trace("proof-db-debug") << "Notify internal " << ai << " " << bi << std::endl;
  if (existsRule(ai, bi))
  {
    // print the proof?
    if (Trace.isOn("proof-db-pf"))
    {
      d_pfStream.str("");
      d_proofPrinting = true;
      unsigned index = 0;
      bool ret = existsRule(ai, bi);
      AlwaysAssert(ret);
      Trace("proof-db-pf") << "; proof of (= " << a << " " << b << ")"
                           << std::endl;
      std::stringstream holdsStream;
      holdsStream << "(check ";
      holdsStream << "(: (holds ";
      ProofDbTermProcess::printLFSCTerm(ai.eqNode(bi),holdsStream);
      holdsStream << ")";
      Trace("proof-db-pf") << holdsStream.str() << std::endl;
      Trace("proof-db-pf") << d_pfStream.str() << std::endl;
      Trace("proof-db-pf") << "))" << std::endl;
      d_proofPrinting = false;
    }
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
  unsigned knownRule = 0;
  if (d_proofPrinting)
  {
    Assert(d_erCache.find(s) != d_erCache.end());
    knownRule = d_erCache[s];
  }
  // check each rule instance
  for (unsigned ruleId : d_ids[n])
  {
    if (d_proofPrinting)
    {
      if (ruleId != knownRule)
      {
        continue;
      }
    }
    Assert(d_proofDbRule.find(ruleId) != d_proofDbRule.end());
    // get the proof rule
    ProofDbRule& pr = d_proofDbRule[ruleId];
    if (d_proofPrinting)
    {
      // construct map from substitution
      std::map<Node, Node> smap;
      for (unsigned i = 0, nvars = vars.size(); i < nvars; i++)
      {
        smap[vars[i]] = subs[i];
      }
      d_pfStream << "(" << pr.d_name;
      // cycle through the variables
      std::map<Node, Node>::iterator itsm;
      for (const Node& v : pr.d_fvs)
      {
        d_pfStream << " ";
        // does it need to be displayed?
        if (pr.d_noOccVars.find(v) != pr.d_noOccVars.end())
        {
          itsm = smap.find(v);
          Assert(itsm != smap.end());
          if (itsm != smap.end())
          {
            ProofDbTermProcess::printLFSCTerm(itsm->second,d_pfStream);
          }
          else
          {
            d_pfStream << "?";
          }
        }
        else
        {
          // can display a hole
          d_pfStream << "_";
        }
      }
    }
    // does the side condition hold?
    bool condSuccess = true;
    Trace("proof-db") << "Check rule " << pr.d_name << std::endl;
    for (const Node& cond : pr.d_cond)
    {
      d_pfStream << " ";
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
    if (d_proofPrinting)
    {
      Assert(condSuccess);
      d_pfStream << ")";
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
