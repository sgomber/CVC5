/*********************                                                        */
/*! \file local_passes.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Local preprocessing passes
 **/

#include "preprocessing/passes/local_passes.h"

#include <unordered_map>
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;
using namespace CVC4::kind;

LocalPasses::LocalPasses(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "local-passes"){};

PreprocessingPassResult LocalPasses::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  unordered_map<Node, Node, NodeHashFunction> cache;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, simplifyAssertion((*assertionsToPreprocess)[i]));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


int LocalPasses::polToCVal( bool has_pol, bool has_epol, bool pol ) 
{ 
  return (has_pol ? (has_epol ? 2 : 1 ) : 0)*( pol ? 1 : -1 ); 
}

void LocalPasses::cValToPol( int cvalue, bool& has_pol, bool& has_epol, bool& pol )
{
  if( cvalue>=0 )
  {
    pol = true;
    has_pol = cvalue>0;
    has_epol = cvalue>1;
  }
  else
  {
    pol = false;
    has_pol = cvalue<0;
    has_epol = cvalue<1;
  }
}

void LocalPasses::getPol(Kind k, unsigned i, bool has_epol, bool pol, bool& new_has_pol, bool& new_has_epol, bool& new_pol)
{
  // should be rewritten by now
  Assert( k!=EXISTS );
  new_has_pol = true;
  new_has_epol = has_epol;
  new_pol = pol;
  if( k==NOT )
  {
    new_pol = !pol;
  }
  else if( k==AND || k==OR || k==SEP_STAR )
  {
    new_has_epol = has_epol && (pol!=( k==OR ));
  }
  else if( k==ITE )
  {
    new_has_pol = (i!=0);
    new_has_epol = false;
  }
  else if( k==IMPLIES )
  {
    new_has_epol = has_epol && !pol;
    new_pol = (i==0 ? !pol : pol);
  }
  else if( k==FORALL )
  {
    new_has_pol = (i==1);
    new_has_epol = false;
  }
  else 
  {
    new_has_pol = false;
    new_has_epol = false;
    new_pol = pol;
  }
}

Node LocalPasses::simplifyAssertion( Node n )
{
  //d_state.reset();
  // get aspects of the state?
  
  NodeManager * nm = NodeManager::currentNM();
  
  std::unordered_map<std::pair<TNode,int>, Node, PairHashFunction<TNode, int, TNodeHashFunction> > visited;
  std::unordered_map<std::pair<TNode,int>, Node, PairHashFunction<TNode, int, TNodeHashFunction> >::iterator it;
  std::vector<std::pair<TNode,int> > visit;
  std::unordered_map<std::pair<TNode,int>, std::vector<std::pair<TNode,int> >, PairHashFunction<TNode, int, TNodeHashFunction> > vchild_map;
  
  std::pair<TNode,int> init_pair = std::pair<TNode,int>(n,polToCVal(true,true,true));
  int no_pol_val = polToCVal(false,false,true);
  
  std::pair<TNode,int> cur_pair;
  TNode cur;
  bool has_pol;
  bool has_epol;
  bool pol;
  bool new_has_pol;
  bool new_has_epol;
  bool new_pol;
  visit.push_back(init_pair);
  do {
    // get current values
    cur_pair = visit.back();
    cur = cur_pair.first;
    cValToPol( cur_pair.second, has_pol, has_epol, pol );
    visit.pop_back();
    
    it = visited.find(cur_pair);
    if (it == visited.end()) {
      Node pre_ret;
      // pre-processing
      for( LocalPass * lp : d_lps )
      {
        pre_ret = lp->preprocess( cur, has_pol, has_epol, pol );
        if( !pre_ret.isNull() )
        {
          visited[cur_pair] = pre_ret;
          break;
        }
      }
      if (pre_ret.isNull()) 
      {
        visited[cur_pair] = Node::null();
        visit.push_back(cur_pair);
        std::vector<std::pair<TNode,int> >& vchildren = vchild_map[cur_pair];
        if( has_pol )
        {
          Kind k = cur.getKind();
          for( unsigned i=0,size=cur.getNumChildren(); i<size; i++ )
          {
            // get the new polarity information
            getPol(k,i,has_epol,pol,new_has_pol,new_has_epol,new_pol);
            vchildren.push_back(std::pair<TNode,int>(cur[i],polToCVal(new_has_pol,new_has_epol,new_pol)));
          }
        }
        else
        {
          for(const Node& cn : cur)
          {
            vchildren.push_back(std::pair<TNode,int>(cn,no_pol_val));
          }
        }
        visit.insert(visit.end(),vchildren.begin(),vchildren.end());
      }
    } 
    else if (it->second.isNull()) 
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back(cur.getOperator());
      }
      std::vector<std::pair<TNode,int> >& vchildren = vchild_map[cur_pair];
      for (const std::pair<TNode,int>& cp : vchildren) 
      {
        it = visited.find(cp);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cp.first != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      Node post_ret;
      // post-processing
      for( LocalPass * lp : d_lps )
      {
        post_ret = lp->preprocess( ret, has_pol, has_epol, pol );
        if( !post_ret.isNull() )
        {
          visited[cur_pair] = post_ret;
          break;
        }
      }
      if (post_ret.isNull()) 
      {
        visited[cur_pair] = ret;
      }
    }
  } while (!visit.empty());
  Assert(visited.find(init_pair) != visited.end());
  Assert(!visited.find(init_pair)->second.isNull());
  return visited[init_pair];
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
