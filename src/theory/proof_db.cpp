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

Node ProofDbTermProcess::toInternal(Node n)
{
  NodeManager * nm = NodeManager::currentNM();
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    it = d_internal.find(cur);

    if (it == d_internal.end()) {
      d_internal[cur] = Node::null();
      visit.push_back(cur);
      for (const Node& cn : cur) {
        visit.push_back(cn);
      }
    } else if (it->second.isNull()) {
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur) {
        it = d_internal.find(cn);
        Assert(it != d_internal.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      Node ret;
      Kind ck = cur.getKind();
      if( ck==CONST_STRING )
      {
        // "ABC" is (str.++ "A" (str.++ "B" "C"))
        const std::vector< unsigned >& vec = cur.getConst<String>().getVec();
        if( vec.size()<=1 )
        {
          ret = cur;
        }
        else
        {
          std::vector< unsigned > v( vec.begin(), vec.end() );
          std::reverse(v.begin(),v.end());
          std::vector< unsigned > tmp;
          tmp.push_back(v[0]);
          ret = nm->mkConst(String(tmp));
          tmp.pop_back();
          for( unsigned i=1, size=v.size(); i<size; i++ )
          {
            tmp.push_back(v[i]);
            ret = nm->mkNode(STRING_CONCAT,nm->mkConst(String(tmp)), ret);
            tmp.pop_back();
          }
        }
      }
      else if( isAssociativeNary(ck) && children.size()>2 )
      {
        Assert(cur.getMetaKind() != kind::metakind::PARAMETERIZED );
        // convert to binary
        std::reverse(children.begin(),children.end());
        ret = children[0];
        for( unsigned i=1, nchild = children.size(); i<nchild; i++ )
        {
          ret = nm->mkNode( ck, children[i], ret );
        }
      }
      else if( childChanged )
      {
        ret = nm->mkNode(ck, children);
      }
      else
      {
        ret = cur;
      }
      d_internal[cur] = ret;
    }
  } while (!visit.empty());
  Assert(d_internal.find(n) != d_internal.end());
  Assert(!d_internal.find(n)->second.isNull());
  return d_internal[n];
}

Node ProofDbTermProcess::toExternal(Node n)
{
  NodeManager * nm = NodeManager::currentNM();
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    it = d_internal.find(cur);

    if (it == d_internal.end()) {
      d_internal[cur] = Node::null();
      visit.push_back(cur);
      for (const Node& cn : cur) {
        visit.push_back(cn);
      }
    } else if (it->second.isNull()) {
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur) {
        it = d_internal.find(cn);
        Assert(it != d_internal.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      Node ret;
      Kind ck = cur.getKind();
      if( isAssociativeNary(ck) )
      {
        Assert( children.size()==2 );
        if( children[1].getKind()==ck )
        {
          // flatten to n-ary
          Node cc = children[1];
          children.pop_back();
          for( const Node& ccc : cc )
          {
            children.push_back(ccc);
          }
          ret = nm->mkNode(ck, children );
        }
        else if( children[1].getKind()==CONST_STRING && children[0].getKind()==CONST_STRING )
        {
          // flatten (non-empty) constants
          const std::vector< unsigned >& v0 = children[0].getConst<String>().getVec();
          const std::vector< unsigned >& v1 = children[1].getConst<String>().getVec();
          if( v0.size()==1 && !v1.empty() )
          {
            std::vector< unsigned > vres;
            vres.push_back(v0[0]);
            vres.insert(vres.end(),v1.begin(),v1.end());
            ret = nm->mkConst(String(vres));
          }
        }
      }
      else if( childChanged )
      {
        ret = nm->mkNode(ck, children);
      }
      if( ret.isNull() )
      {
        ret = cur;
      }
      d_internal[cur] = ret;
    }
  } while (!visit.empty());
  Assert(d_internal.find(n) != d_internal.end());
  Assert(!d_internal.find(n)->second.isNull());
  return d_internal[n];
}
  
bool ProofDbTermProcess::isAssociativeNary(Kind k)
{
  return k==AND || k==OR || k==STRING_CONCAT;
}
  
void ProofDbRule::init(const std::string& name, Node cond, Node eq)
{
  d_name = name;
  d_cond = cond;
  d_eq = eq;
}

ProofDb::ProofDb() : d_idCounter(1), d_notify(*this) {}

void ProofDb::registerRules(const std::map<Node, std::string>& rules)
{
  // add each of the rules to the database
  for (const std::pair<const Node, std::string>& rr : rules)
  {
    Node r = rr.first;
    AlwaysAssert(r.getKind() == IMPLIES);

    // must canonize
    Trace("proof-db") << "Add rule " << r[1] << std::endl;
    Node cr = d_canon.getCanonicalTerm(r);

    Node cond = cr[0];
    Node eq = cr[1];

    // add to discrimination tree
    Trace("proof-db-debug") << "Add (Canonical) rule " << eq << std::endl;
    d_mt.addTerm(eq);

    // remember rules
    d_ids[eq].push_back(d_idCounter);
    d_proofDbRule[d_idCounter].init(rr.second, cond, eq);
    d_idCounter++;
  }
}

bool ProofDb::existsRule(Node a, Node b, unsigned& index)
{
  if (a == b)
  {
    // reflexivity
    return true;
  }
  if (b.isConst())
  {
    // nullary symbols should not rewrite to constants
    Assert(a.getNumChildren() != 0);
    bool allConst = true;
    for (const Node& ac : a)
    {
      Node ace = d_pdtp.toExternal(ac);
      if (!ace.isConst())
      {
        allConst = false;
        break;
      }
    }
    if (allConst)
    {
      // evaluation
      return true;
    }
  }
  Kind ak = a.getKind();
  Kind bk = b.getKind();
  if (ak == EQUAL && a[0] == a[1])
  {
    Assert(b.isConst() && b.getConst<bool>());
    // rewriting reflexive equality to true
    return true;
  }
  if (ak == EQUAL && bk == EQUAL)
  {
    if (a[0] == b[1] && b[0] == a[1])
    {
      // symmetry of equality
      return true;
    }
  }
  TheoryId at = Theory::theoryOf(a);
  if( at==THEORY_ARITH )
  {
    // normalization?
    return true;
  }
  if( at==THEORY_BOOL )
  {
    // normalization? ignore for now
    return true;
  }
  Node eq = a.eqNode(b);
  // is an instance of existing rule?
  if (!d_mt.getMatches(eq, &d_notify))
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
    Node cond = pr.d_cond;
    if (cond.isConst() && cond.getConst<bool>())
    {
      // successfully found instance of rule
      if( Trace.isOn("proof-db-infer") )
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
