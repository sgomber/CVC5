/*********************                                                        */
/*! \file gen_lit_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Generalized literal info
 **/

#include "theory/quantifiers/gen_lit_info.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void GLitInfo::initialize(InstExplainInst* iei) { d_iei = iei; }

bool GLitInfo::initialize(TNode a, const GLitInfo& ga, TNode b, const GLitInfo& gb)
{
  // copy info from ga
  d_iei = ga.d_iei;
  d_subs_modify = ga.d_subs_modify;
  return merge(a,b,gb);
}

bool GLitInfo::merge(TNode a, TNode b, const GLitInfo& gb)
{
  Trace("ied-ginfo") << "GLitInfo::merge, a : " << a << std::endl;
  Trace("ied-ginfo") << "GLitInfo::merge, b : " << b << std::endl;
  // the visit cache and indicates unifier information
  std::map< Node, std::unordered_set< Node, NodeHashFunction > > visited;
  std::vector< Node > avisit;
  std::vector< Node > bvisit;
  std::map<TNode, Node>::const_iterator it;
  std::map< Node, std::unordered_set< Node, NodeHashFunction > >::iterator itv;
  avisit.push_back(a);
  bvisit.push_back(b);
  TNode cura;
  TNode curb;
  do {
    cura = avisit.back();
    avisit.pop_back();
    curb = bvisit.back();
    bvisit.pop_back();
    std::unordered_set< Node, NodeHashFunction >& va = visited[cura];
    if (va.find(curb) == va.end()) {
      va.insert(curb);
      Trace("ied-ginfo-debug") << "Match a:" << cura << std::endl;
      Trace("ied-ginfo-debug") << "Match b:" << curb << std::endl;
      bool abv = cura.getKind()==BOUND_VARIABLE;
      bool bbv = curb.getKind()==BOUND_VARIABLE;
      // TODO: check that it is bound by the quantified formula

      TNode av = cura;
      if( abv )
      {
        it = d_subs_modify.find(cura);
        if( it!=d_subs_modify.end() )
        {
          av = it->second;
          abv = false;
        }
      }
      TNode bv = curb;
      if( bbv )
      {
        it = gb.d_subs_modify.find(curb);
        if( it!=gb.d_subs_modify.end() )
        {
          bv = it->second;
          bbv = false;
        }
      }
      if( abv )
      {
        // two bound variables
        if( bbv )
        {
          // store reversed to ensure that we bind cura if curb becomes bound later
          visited[curb].insert(cura);
          if( visited[curb].size()>1 )
          {
            Trace("ied-ginfo") << "GLitInfo::merge: Fail: induced equality on " << curb << std::endl;
            return false;
          }
        }
        else
        {
          // bind a
          Trace("ied-ginfo") << "GLitInfo::merge: bind " << cura << " -> " << bv << std::endl;
          d_subs_modify[cura] = bv;
        }
      }
      else
      {
        if( bbv )
        {
          // must go back and bind all occurrences it was equal to
          itv = visited.find(curb);
          if( itv!=visited.end() )
          {
            for( TNode x : itv->second )
            {
              if( d_subs_modify.find(x)!=d_subs_modify.end() )
              {
                // bound to different things, fail?
                Trace("ied-ginfo") << "GLitInfo::merge: Fail: " << cura << " == " << curb << ", where " << curb << " == " << x << std::endl;
                Trace("ied-ginfo") << "GLitInfo::merge: which contradicts ( " << d_subs_modify[x] << " == ) " << x << " == " << curb << "( == " << bv << " ) " << std::endl;
                return false;
              }
              else
              {
                Trace("ied-ginfo") << "GLitInfo::merge: bind (backwards) " << x << " -> " << av << std::endl;
                d_subs_modify[x] = av;
              }
            }
          }
        }
        else if( av!=bv )
        {        
          // recurse
          if( av.hasOperator() )
          {
            if( !bv.hasOperator() || bv.getOperator()!=av.getOperator() || bv.getNumChildren()!=av.getNumChildren() )
            {
              Trace("ied-ginfo") << "GLitInfo::merge: Fail: clash ( " << av << " == ) " << cura << " == " << curb << "( == " << bv << " ) " << std::endl;
              // wrong operators, should only happen if we within a substitution
              Assert( cura.getKind()==BOUND_VARIABLE || curb.getKind()==BOUND_VARIABLE );
              return false;
            }
            for( unsigned i=0, nchild=cura.getNumChildren(); i<nchild; i++ )
            {
              if( a[i]!=b[i] )
              {
                avisit.push_back(a[i]);
                bvisit.push_back(b[i]);
              }
            }
          }
          else
          {
            Trace("ied-ginfo") << "GLitInfo::merge: Fail: operator ( " << av << " == ) " << cura << " == " << curb << "( == " << bv << " ) " << std::endl;
            // not equal and a is a variable, fail
            return false;
          }
        }
      }
    }
  } while (!avisit.empty());
  
  Trace("ied-ginfo") << "GLitInfo::merge: Success!" << std::endl;
  return true;
}

bool GLitInfo::drop(TNode b)
{
  // drop free variables
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
