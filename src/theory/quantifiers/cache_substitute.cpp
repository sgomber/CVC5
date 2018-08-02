/*********************                                                        */
/*! \file cache_substitute.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of cache_substitute
 **/

#include "theory/quantifiers/cache_substitute.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void CacheSubstitute::initialize( Node n, const std::vector< Node >& vars ){
  // intialize entry for null node 
  // this is a placeholder to shift indices by one
  d_kinds.push_back( UNDEFINED_KIND );
  d_cons_ptr.push_back( std::vector< unsigned >() );
  d_data.push_back( std::vector< Node >() );
  d_data_out.push_back( Node::null() );
  
  // map from nodes to ids
  std::unordered_map<TNode, unsigned, TNodeHashFunction> id_map;
  // initialize variables
  for( const Node& v : vars ){
    id_map[v] = d_kinds.size();
    d_kinds.push_back( UNDEFINED_KIND );
    d_cons_ptr.push_back( std::vector< unsigned >() );
    d_data.push_back( std::vector< Node >() );
    d_data_out.push_back( Node::null() );
  }
  
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::unordered_map<TNode, bool, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end()) {
      visited[cur] = false;
      visit.push_back(cur);
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push_back(cur[i]);
      }
    }else if( !it->second ){
      std::vector< Node > data;
      if( cur.getMetaKind() == kind::metakind::PARAMETERIZED ){
        data.push_back(cur.getOperator());
      }
      for( const Node& nc : cur ){
        data.push_back(nc);
      }
      
      //process the data
      bool contains_var = false;
      std::vector< unsigned > cptr;
      for( const Node& nc : data ){
        std::unordered_map<TNode, unsigned, TNodeHashFunction>::iterator it = id_map.find(nc);
        if( it!=id_map.end() ){
          cptr.push_back(it->second);
          contains_var = true;
        }else{
          cptr.push_back(0);
        }          
      }
      
      if( contains_var ){
        id_map[cur] = d_kinds.size();
        d_kinds.push_back(cur.getKind());
        d_cons_ptr.push_back(cptr);
        d_data.push_back(data);
        d_data_out.push_back(Node::null());
      }
      visited[cur] = true;
    }
  } while (!visit.empty());
  
  // degenerate case : if n does not contain a variable from vars, then
  // this class will always return n. 
  if( d_data.size()==vars.size()+1 ){
    d_data_out.push_back(n);
  }
}

Node CacheSubstitute::getSubstitute( const std::vector< Node >& subs ){
  for( unsigned i=0, size = subs.size(); i<size; i++ ){
    d_data_out[i+1] = subs[i];
  }
  NodeManager * nm = NodeManager::currentNM();
  for( unsigned j=subs.size()+1, size = d_data.size(); j<size; j++ ){
    // update data
    std::vector< unsigned >& cptr = d_cons_ptr[j];
    for( unsigned k=0, sizec = cptr.size(); k<sizec; k++ ){
      unsigned index = cptr[k];
      if( index!=0 ){
        d_data[j][k] = d_data_out[index];
      }
    }
    // make data out
    d_data_out[j] = nm->mkNode( d_kinds[j], d_data[j] );
  }
  return d_data_out.back();
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
