#include "perf_tests.h"

#include "options/smt_options.h"

namespace CVC4 {
  
bool findUSetIterStack( TNode n, TNode v ){
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::stack<TNode> visit;
  TNode cur;
  visit.push(n);
  do {
    cur = visit.top();
    visit.pop();

    if (visited.find(cur) == visited.end()) {
      visited.insert(cur);
      if( cur==v ){
        return true;
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push(cur[i]);
      }
    }
  } while (!visit.empty());
  return false;
}

bool findVecIterStack( TNode n, TNode v ){
  std::vector<TNode> visited;
  std::stack<TNode> visit;
  TNode cur;
  visit.push(n);
  do {
    cur = visit.top();
    visit.pop();

    if (std::find(visited.begin(),visited.end(),cur) == visited.end()) {
      visited.push_back(cur);
      if( cur==v ){
        return true;
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push(cur[i]);
      }
    }
  } while (!visit.empty());
  return false;
}

bool findMapIterStack( TNode n, TNode v ){
  std::map<TNode, bool> visited;
  std::stack<TNode> visit;
  TNode cur;
  visit.push(n);
  do {
    cur = visit.top();
    visit.pop();

    if (visited.find(cur) == visited.end()) {
      visited[cur] = true;
      if( cur==v ){
        return true;
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push(cur[i]);
      }
    }
  } while (!visit.empty());
  return false;
}

bool findUMapIterStack( TNode n, TNode v ){
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::stack<TNode> visit;
  TNode cur;
  visit.push(n);
  do {
    cur = visit.top();
    visit.pop();

    if (visited.find(cur) == visited.end()) {
      visited[cur] = true;
      if( cur==v ){
        return true;
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push(cur[i]);
      }
    }
  } while (!visit.empty());
  return false;
}

bool findUSetRec( TNode n, TNode v, std::unordered_set<TNode, TNodeHashFunction>& visited ){
  if( visited.find( n )==visited.end() ){
    visited.insert(n);
    if( n==v ){
      return true;
    }
    
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( findUSetRec( n[i], v, visited ) ){
        return true;
      }
    }
  }
  return false;
}

bool findVecRec( TNode n, TNode v, std::vector< TNode >& visited ){
  if( std::find( visited.begin(), visited.end(), n )==visited.end() ){
    visited.push_back( n );
    if( n==v ){
      return true;
    }
    
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( findVecRec( n[i], v, visited ) ){
        return true;
      }
    }
  }
  return false;
}

bool findMapRec( TNode n, TNode v, std::map< TNode, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n==v ){
      return true;
    }
    
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( findMapRec( n[i], v, visited ) ){
        return true;
      }
    }
  }
  return false;
}

bool findUMapRec( TNode n, TNode v, std::unordered_map< TNode, bool, TNodeHashFunction >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n==v ){
      return true;
    }
    
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( findUMapRec( n[i], v, visited ) ){
        return true;
      }
    }
  }
  return false;
}


bool findUSetIterVec( TNode n, TNode v ){
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();

    if (visited.find(cur) == visited.end()) {
      visited.insert(cur);
      if( cur==v ){
        return true;
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push_back(cur[i]);
      }
    }
  } while (!visit.empty());
  return false;
}

bool findVecIterVec( TNode n, TNode v ){
  std::vector<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();

    if (std::find(visited.begin(),visited.end(),cur) == visited.end()) {
      visited.push_back(cur);
      if( cur==v ){
        return true;
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push_back(cur[i]);
      }
    }
  } while (!visit.empty());
  return false;
}

bool findMapIterVec( TNode n, TNode v ){
  std::map<TNode, bool> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();

    if (visited.find(cur) == visited.end()) {
      visited[cur] = true;
      if( cur==v ){
        return true;
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push_back(cur[i]);
      }
    }
  } while (!visit.empty());
  return false;
}

bool findUMapIterVec( TNode n, TNode v ){
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();

    if (visited.find(cur) == visited.end()) {
      visited[cur] = true;
      if( cur==v ){
        return true;
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push_back(cur[i]);
      }
    }
  } while (!visit.empty());
  return false;
}

void PerfTest::runTestFindDataStructures()
{
  Trace("ajr-test") << "----Test find..." << std::endl;
  Trace("ajr-test") << "  Making depth " << d_depth << " term..." << std::endl;
  Node r = mkRandom(d_depth,d_rf);
  unsigned index = d_vars.size();
  Trace("ajr-test") << "  Number of variables introduced was " << index << "..." << std::endl;
  // make double the vars (find succeeds half the time)
  for( unsigned i=0; i<index; i++ ){
    std::stringstream ss;
    ss << "nt" << d_vars.size();
    d_vars.push_back( NodeManager::currentNM()->mkBoundVar( ss.str(), NodeManager::currentNM()->realType() ) );
  }
  index = d_vars.size();
  std::random_shuffle( d_vars.begin(), d_vars.end() );
  
  unsigned totalTests = double(d_totalTestsF)*10000000.0/(double)(index);
  Trace("ajr-test") << "Total tests is " << totalTests << "..." << std::endl;
  
  unsigned tests = 0;
  long count = 0;
  if( d_testType==0 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<index; i++ ){
        if( findUSetIterStack( r, d_vars[i] ) ){
          count++;
        }
        tests++;
      }
    }
  }else if( d_testType==1 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<index; i++ ){
        if( findVecIterStack( r, d_vars[i] ) ){
          count++;
        }
        tests++;
      }
    }
  }else if( d_testType==2 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<index; i++ ){
        if( findMapIterStack( r, d_vars[i] ) ){
          count++;
        }
        tests++;
      }
    }
  }else if( d_testType==3 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<index; i++ ){
        if( findUMapIterStack( r, d_vars[i] ) ){
          count++;
        }
        tests++;
      }
    }
  }else if( d_testType==4 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<index; i++ ){
        std::unordered_set<TNode, TNodeHashFunction> visited;
        if( findUSetRec( r, d_vars[i], visited ) ){
          count++;
        }
        tests++;
      }
    }
  }else if( d_testType==5 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<index; i++ ){
        std::vector<TNode> visited;
        if( findVecRec( r, d_vars[i], visited ) ){
          count++;
        }
        tests++;
      }
    }
  }else if( d_testType==6 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<index; i++ ){
        std::map<TNode, bool> visited;
        if( findMapRec( r, d_vars[i], visited ) ){
          count++;
        }
        tests++;
      }
    }
  }else if( d_testType==7 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<index; i++ ){
        std::unordered_map<TNode, bool, TNodeHashFunction> visited;
        if( findUMapRec( r, d_vars[i], visited ) ){
          count++;
        }
        tests++;
      }
    }
  }else if( d_testType==8 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<index; i++ ){
        if( findUSetIterVec( r, d_vars[i] ) ){
          count++;
        }
        tests++;
      }
    }
  }else if( d_testType==9 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<index; i++ ){
        if( findVecIterVec( r, d_vars[i] ) ){
          count++;
        }
        tests++;
      }
    }
  }else if( d_testType==10 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<index; i++ ){
        if( findMapIterVec( r, d_vars[i] ) ){
          count++;
        }
        tests++;
      }
    }
  }else if( d_testType==11 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<index; i++ ){
        if( findUMapIterVec( r, d_vars[i] ) ){
          count++;
        }
        tests++;
      }
    }
  }else{
    std::stringstream ss;
    ss << "Unknown test type " << d_testType << " for find test";
    Unhandled(ss.str());
  }
  Trace("ajr-test") << "Count is " << count << std::endl;  
}

}
