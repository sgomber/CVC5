#include "perf_tests.h"

#include "options/smt_options.h"

namespace CVC4 {
  
void PerfTest::runTestCountTNode()
{
  Trace("ajr-test") << "----Test count..." << std::endl;
  initializeVars(d_depth, d_rf);
  NodeManager * nm = NodeManager::currentNM();
  
  // 10^8 tests
  long totalTests = double(d_totalTestsF)*100000000.0/(double)(d_depth);
  Trace("ajr-test") << "---Total tests is " << totalTests << "..." << std::endl;
  long tests = 0;
  long count = 0;
  
  // 0 : counter over TNode 
  // 1 : counter+getNumChildren over TNode 
  // 2 : iterator over TNode 
  // 3 : range iterator over TNode
  // 4 : const reference range iterator over TNode
  // 5 : auto range iterator over TNode
  Trace("ajr-test") << "----Test count (TNode version)..." << std::endl;
  std::vector< TypeNode > types;
  for( unsigned i=0; i<d_vars.size(); i++ ){
    types.push_back( d_vars[i].getType() );
  }
  TypeNode ftn = nm->mkFunctionType( types, nm->realType() );
  Node nff = nm->mkBoundVar( "f", ftn );
  TNode ff = nff;
  std::vector< TNode > fchildren;
  fchildren.push_back( ff );
  fchildren.insert( fchildren.end(), d_vars.begin(), d_vars.end() );
  Node nf = nm->mkNode( kind::APPLY_UF, fchildren );
  TNode f = nf;
  
  if( d_testType==0 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<f.getNumChildren(); i++ ){
        if( testVar(f[i]) ){
          count++;
        }
      }
      tests++;
    }
  }else if( d_testType==1 ){
    while( tests<totalTests ){
      for( unsigned i=0, size = f.getNumChildren(); i<size; i++ ){
        if( testVar(f[i]) ){
          count++;
        }
      }
      tests++;
    }
  }else if( d_testType==2 ){
    while( tests<totalTests ){
      for( TNode::iterator it = f.begin(); it != f.end(); ++it ){
        if( testVar(*it) ){
          count++;
        }
      }
      tests++;
    }
  }else if( d_testType==3 ){
    while( tests<totalTests ){
      for( TNode v : f ){
        if( testVar(v) ){
          count++;
        }
      }
      tests++;
    }
  }else if( d_testType==4 ){
    while( tests<totalTests ){
      for( const TNode& v : f ){
        if( testVar(v) ){
          count++;
        }
      }
      tests++;
    }
  }else if( d_testType==5 ){
    while( tests<totalTests ){
      for( auto v : f ){
        if( testVar(v) ){
          count++;
        }
      }
      tests++;
    }
  }else if( d_testType==6 ){
    while( tests<totalTests ){
      for( const TNode v : f ){
        if( testVar(v) ){
          count++;
        }
      }
      tests++;
    }
  }else if( d_testType==7 ){
    while( tests<totalTests ){
      for( const auto& v : f ){
        if( testVar(v) ){
          count++;
        }
      }
      tests++;
    }   
  }else if( d_testType==8 ){
    while( tests<totalTests ){
      for( const auto v : f ){
        if( testVar(v) ){
          count++;
        }
      }
      tests++;
    }
  }else{
    std::stringstream ss;
    ss << "Unknown test type " << d_testType << " for count node test";
    Unhandled(ss.str());
  }
  Trace("ajr-test") << "Count is " << count << std::endl;  
}

}
