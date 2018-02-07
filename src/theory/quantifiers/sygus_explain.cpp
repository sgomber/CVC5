/*********************                                                        */
/*! \file sygus_explain.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of techniques for sygus explanations
 **/

#include "theory/quantifiers/sygus_explain.h"

#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers/term_database_sygus.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void TermRecBuild::addTerm(Node n)
{
  d_term.push_back(n);
  std::vector<Node> currc;
  d_kind.push_back(n.getKind());
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    currc.push_back(n.getOperator());
    d_has_op.push_back(true);
  }
  else
  {
    d_has_op.push_back(false);
  }
  for (unsigned i = 0; i < n.getNumChildren(); i++)
  {
    currc.push_back(n[i]);
  }
  d_children.push_back(currc);
}

void TermRecBuild::init(Node n)
{
  Assert(d_term.empty());
  addTerm(n);
}

void TermRecBuild::push(unsigned p)
{
  Assert(!d_term.empty());
  unsigned curr = d_term.size() - 1;
  Assert(d_pos.size() == curr);
  Assert(d_pos.size() + 1 == d_children.size());
  Assert(p < d_term[curr].getNumChildren());
  addTerm(d_term[curr][p]);
  d_pos.push_back(p);
}

void TermRecBuild::pop()
{
  Assert(!d_pos.empty());
  d_pos.pop_back();
  d_kind.pop_back();
  d_has_op.pop_back();
  d_children.pop_back();
  d_term.pop_back();
}

void TermRecBuild::replaceChild(unsigned i, Node r)
{
  Assert(!d_term.empty());
  unsigned curr = d_term.size() - 1;
  unsigned o = d_has_op[curr] ? 1 : 0;
  d_children[curr][i + o] = r;
}

Node TermRecBuild::getChild(unsigned i)
{
  unsigned curr = d_term.size() - 1;
  unsigned o = d_has_op[curr] ? 1 : 0;
  return d_children[curr][i + o];
}

Node TermRecBuild::build(unsigned d)
{
  Assert(d_pos.size() + 1 == d_term.size());
  Assert(d < d_term.size());
  int p = d < d_pos.size() ? d_pos[d] : -2;
  std::vector<Node> children;
  unsigned o = d_has_op[d] ? 1 : 0;
  for (unsigned i = 0; i < d_children[d].size(); i++)
  {
    Node nc;
    if (p + o == i)
    {
      nc = build(d + 1);
    }
    else
    {
      nc = d_children[d][i];
    }
    children.push_back(nc);
  }
  return NodeManager::currentNM()->mkNode(d_kind[d], children);
}


VirtualSygusTerm * VirtualSygusTerm::addTester(TermDbSygus* tdb, TypeNode tn, Node tst )
{
  Node a;
  int cindex = datatypes::DatatypesRewriter::isTester( tst, a );
  Assert( cindex!=-1 );
  
  std::vector< Node > chain;
  while( a.getKind()==APPLY_SELECTOR_TOTAL )
  {
    chain.push_back( a );
    a = a[0];
  }
  std::reverse( chain.begin(), chain.end() );
  
  VirtualSygusTerm * curr = this;
  for( const Node& sel : chain )
  {
    Expr selExpr = sel.getOperator().toExpr();
    const Datatype& dt = Datatype::datatypeOf(selExpr);
    Assert( curr->d_cindex>=0 );
    const DatatypeConstructor& dtc = dt[curr->d_cindex];
    int selectorIndex = dtc.getSelectorIndexInternal(selExpr);
    Assert( selectorIndex>=0 );
    curr = &(curr->d_children[selectorIndex]);
  }
  curr->d_cindex = cindex;
  return curr;
}

void VirtualSygusTerm::setTerm(TermDbSygus* tdb, Node n)
{
  if( n.getKind()==APPLY_CONSTRUCTOR )
  {
    d_build_term = Node::null();
    d_children.clear();
    Node constructor = n.getOperator();
    d_cindex = Datatype::indexOf(constructor.toExpr());
    for( unsigned i=0,size=n.getNumChildren(); i<size; i++ )
    {
      d_children[i].setTerm(tdb,n[i]);
    }
  }
  else
  {
    d_build_term = n;
  }
}

void VirtualSygusTerm::clear()
{
  d_build_term = Node::null();
  d_cindex = -1;
  d_children.clear();
}

Node VirtualSygusTerm::build(TermDbSygus* tdb, TypeNode tn)
{
  std::map<TypeNode, int> var_count;
  std::map< Node, std::vector< VirtualSygusTerm * > > subterms;
  return build(tdb,tn,var_count, subterms);
}

Node VirtualSygusTerm::build(TermDbSygus* tdb, TypeNode tn, std::map<TypeNode,int>& var_count, std::map< Node, std::vector< VirtualSygusTerm * > >& subterms)
{
  Trace("ajr-temp") << "...compute for " << tn << std::endl;
  Assert( tn.isDatatype() );
  Node ret;
  if( !d_build_term.isNull() )
  {
    ret = d_build_term;
  }
  else if( d_cindex==-1 )
  {
    ret = tdb->getFreeVarInc(tn,var_count, true);
  }
  else
  {
    const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
    Assert( d_cindex<(int)dt.getNumConstructors() );
    const DatatypeConstructor& dtc = dt[d_cindex];
    Trace("ajr-temp") << "...constructor " << dtc << std::endl;
    std::vector< Node > children;
    children.push_back( Node::fromExpr(dtc.getConstructor()) );
    for( unsigned i=0, nargs=dtc.getNumArgs(); i<nargs; i++ )
    {
      TypeNode ctn = tdb->getArgType( dtc, i );
      Node c;
      std::map< unsigned, VirtualSygusTerm >::iterator itc = d_children.find(i);
      if( itc != d_children.end() )
      {
        c = itc->second.build(tdb, ctn, var_count, subterms );
      }
      else
      {
        c = tdb->getFreeVarInc(ctn,var_count, true);
      }
      Assert( !c.isNull() );
      Assert( c.getType()==ctn );
      children.push_back( c );
    }
    ret = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
  }
  Trace("ajr-temp") << "...return " << ret << std::endl;
  subterms[ret].push_back( this );
  return ret;
}

void SygusExplain::getExplanationForConstantEquality(Node n,
                                                     Node vn,
                                                     std::vector<Node>& exp)
{
  std::map<unsigned, bool> cexc;
  getExplanationForConstantEquality(n, vn, exp, cexc);
}

void SygusExplain::getExplanationForConstantEquality(
    Node n, Node vn, std::vector<Node>& exp, std::map<unsigned, bool>& cexc)
{
  Assert(vn.getKind() == kind::APPLY_CONSTRUCTOR);
  Assert(n.getType() == vn.getType());
  TypeNode tn = n.getType();
  Assert(tn.isDatatype());
  const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
  int i = Datatype::indexOf(vn.getOperator().toExpr());
  Node tst = datatypes::DatatypesRewriter::mkTester(n, i, dt);
  exp.push_back(tst);
  for (unsigned j = 0; j < vn.getNumChildren(); j++)
  {
    if (cexc.find(j) == cexc.end())
    {
      Node sel = NodeManager::currentNM()->mkNode(
          kind::APPLY_SELECTOR_TOTAL,
          Node::fromExpr(dt[i].getSelectorInternal(tn.toType(), j)),
          n);
      getExplanationForConstantEquality(sel, vn[j], exp);
    }
  }
}

Node SygusExplain::getExplanationForConstantEquality(Node n, Node vn)
{
  std::map<unsigned, bool> cexc;
  return getExplanationForConstantEquality(n, vn, cexc);
}

Node SygusExplain::getExplanationForConstantEquality(
    Node n, Node vn, std::map<unsigned, bool>& cexc)
{
  std::vector<Node> exp;
  getExplanationForConstantEquality(n, vn, exp, cexc);
  Assert(!exp.empty());
  return exp.size() == 1 ? exp[0]
                         : NodeManager::currentNM()->mkNode(kind::AND, exp);
}

// we have ( n = vn => eval( n ) = bvr ) ^ vn != vnr , returns exp such that exp
// => ( eval( n ) = bvr ^ vn != vnr )
void SygusExplain::getExplanationFor(TermRecBuild& trb,
                                     Node n,
                                     Node vn,
                                     std::vector<Node>& exp,
                                     std::map<TypeNode, int>& var_count,
                                     SygusInvarianceTest& et,
                                     Node vnr,
                                     Node& vnr_exp,
                                     int& sz)
{
  Assert(vnr.isNull() || vn != vnr);
  Assert(vn.getKind() == APPLY_CONSTRUCTOR);
  Assert(vnr.isNull() || vnr.getKind() == APPLY_CONSTRUCTOR);
  Assert(n.getType() == vn.getType());
  TypeNode ntn = n.getType();
  std::map<unsigned, bool> cexc;
  // for each child, 
  // check whether replacing that child by a fresh variable
  // also satisfies the invariance test.
  for (unsigned i = 0; i < vn.getNumChildren(); i++)
  {
    TypeNode xtn = vn[i].getType();
    Node x = d_tdb->getFreeVarInc(xtn, var_count);
    trb.replaceChild(i, x);
    Node nvn = trb.build();
    Assert(nvn.getKind() == kind::APPLY_CONSTRUCTOR);
    if (et.is_invariant(d_tdb, nvn, x))
    {
      cexc[i] = true;
      // we are tracking term size if positive
      if (sz >= 0)
      {
        int s = d_tdb->getSygusTermSize(vn[i]);
        sz = sz - s;
      }
    }
    else
    {
      trb.replaceChild(i, vn[i]);
    }
  }
  const Datatype& dt = ((DatatypeType)ntn.toType()).getDatatype();
  int cindex = Datatype::indexOf(vn.getOperator().toExpr());
  Assert(cindex >= 0 && cindex < (int)dt.getNumConstructors());
  Node tst = datatypes::DatatypesRewriter::mkTester(n, cindex, dt);
  exp.push_back(tst);
  // if the operator of vn is different than vnr, then disunification obligation
  // is met
  if (!vnr.isNull())
  {useSygusType
    if (vnr.getOperator() != vn.getOperator())
    {
      vnr = Node::null();
      vnr_exp = NodeManager::currentNM()->mkConst(true);
    }
  }
  for (unsigned i = 0; i < vn.getNumChildren(); i++)
  {
    Node sel = NodeManager::currentNM()->mkNode(
        kind::APPLY_SELECTOR_TOTAL,
        Node::fromExpr(dt[cindex].getSelectorInternal(ntn.toType(), i)),
        n);
    Node vnr_c = vnr.isNull() ? vnr : (vn[i] == vnr[i] ? Node::null() : vnr[i]);
    if (cexc.find(i) == cexc.end())
    {
      trb.push(i);
      Node vnr_exp_c;
      getExplanationFor(
          trb, sel, vn[i], exp, var_count, et, vnr_c, vnr_exp_c, sz);
      trb.pop();
      if (!vnr_c.isNull())
      {
        Assert(!vnr_exp_c.isNull());
        if (vnr_exp_c.isConst() || vnr_exp.isNull())
        {
          // recursively satisfied the disunification obligation
          if (vnr_exp_c.isConst())
          {
            // was successful, don't consider further
            vnr = Node::null();
          }
          vnr_exp = vnr_exp_c;
        }
      }
    }
    else
    {
      // if excluded, we may need to add the explanation for this
      if (vnr_exp.isNull() && !vnr_c.isNull())
      {
        vnr_exp = getExplanationForConstantEquality(sel, vnr[i]);
      }
    }
  }
}

void SygusExplain::getExplanationFor(Node n,
                                     Node vn,
                                     std::vector<Node>& exp,
                                     SygusInvarianceTest& et,
                                     Node vnr,
                                     unsigned& sz)
{
  // naive :
  // return getExplanationForConstantEquality( n, vn, exp );

  // set up the recursion object
  std::map<TypeNode, int> var_count;
  TermRecBuild trb;
  trb.init(vn);
  Node vnr_exp;
  int sz_use = sz;
  getExplanationFor(trb, n, vn, exp, var_count, et, vnr, vnr_exp, sz_use);
  
  
  Trace("sygus-eq-gen") << "Get explanation for " << n << " == " << vn << " returned: " << std::endl;
  TypeNode tn = n.getType();
  VirtualSygusTerm vst;
  // map from virtual sygus terms to their explanations (tester applied to 
  // selector chain)
  std::map< VirtualSygusTerm *, Node > vst_exp;
  for( const Node& e : exp )
  {
    Trace("sygus-eq-gen") << "  " << e << std::endl;
    VirtualSygusTerm * vsg = vst.addTester( d_tdb, tn, e );
    vst_exp[vsg] = e;
    Trace("sygus-eq-gen") << "  ...returned " << vsg << std::endl;
  }
  var_count.clear();
  /*
  std::map< Node, std::vector< VirtualSygusTerm * > > subterms;
  Trace("sygus-eq-gen") << "Build virtual sygus term..." << std::endl;
  Node vsb = vst.build( d_tdb, tn, var_count, subterms );
  Trace("sygus-eq-gen") << "Virtual sygus term built : " << vsb << std::endl;
  for( const std::pair< Node, std::vector< VirtualSygusTerm * > >& st : subterms )
  {
    if( st.second.size()>1 )
    {
      Node t = st.first;
      Trace("sygus-eq-gen") << "..." << st.second.size() << " subterms for " << t << std::endl;
    }
  }
  */
  
  Assert(sz_use >= 0);
  sz = sz_use;
  Assert(vnr.isNull() || !vnr_exp.isNull());
  if (!vnr_exp.isNull() && !vnr_exp.isConst())
  {
    exp.push_back(vnr_exp.negate());
  }
}

void SygusExplain::getExplanationFor(Node n,
                                     Node vn,
                                     std::vector<Node>& exp,
                                     SygusInvarianceTest& et)
{
  int sz = -1;
  std::map<TypeNode, int> var_count;
  TermRecBuild trb;
  trb.init(vn);
  Node vnr;
  Node vnr_exp;
  getExplanationFor(trb, n, vn, exp, var_count, et, vnr, vnr_exp, sz);
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
