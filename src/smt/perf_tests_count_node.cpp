#include "perf_tests.h"

#include "options/smt_options.h"

namespace CVC4 {
  
void PerfTest::runTestCountNode()
{
  Trace("ajr-test") << "----Test count..." << std::endl;
  initializeVars(d_depth, d_rf);
    
  long totalTests = double(d_totalTestsF)*100000000.0/(double)(d_depth);
  Trace("ajr-test") << "---Total tests is " << totalTests << "..." << std::endl;
  long tests = 0;
  long count = 0;
  
  // 0 : counter over Node 
  // 1 : counter+getNumChildren over Node 
  // 2 : iterator over Node 
  // 3 : range iterator over Node
  // 4 : const reference range iterator over Node
  // 5 : auto range iterator over Node
  Trace("ajr-test") << "----Test count (Node version)..." << std::endl;
  std::vector< TypeNode > types;
  for( unsigned i=0; i<d_vars.size(); i++ ){
    types.push_back( d_vars[i].getType() );
  }
  TypeNode ftn = NodeManager::currentNM()->mkFunctionType( types, NodeManager::currentNM()->realType() );
  Node ff = NodeManager::currentNM()->mkBoundVar( "f", ftn );
  std::vector< Node > fchildren;
  fchildren.push_back( ff );
  fchildren.insert( fchildren.end(), d_vars.begin(), d_vars.end() );
  Node f = NodeManager::currentNM()->mkNode( kind::APPLY_UF, fchildren );
  
  if( !options::useUnknown() ){
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
        for( Node::iterator it = f.begin(); it != f.end(); ++it ){
          if( testVar(*it) ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==3 ){
      while( tests<totalTests ){
        for( Node v : f ){
          if( testVar(v) ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==4 ){
      while( tests<totalTests ){
        for( const Node& v : f ){
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
    }
  }else{
    if( d_testType==0 ){
      while( tests<totalTests ){
        for( unsigned i=0; i<f.getNumChildren(); i++ ){
          if( testVar(f[i]) ){
            count++;
          }
          if( d_unk ){
            d_vars.push_back(f[i]);
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
          if( d_unk ){
            d_vars.push_back(f[i]);
          }
        }
        tests++;
      }
    }else if( d_testType==2 ){
      while( tests<totalTests ){
        for( Node::iterator it = f.begin(); it != f.end(); ++it ){
          if( testVar(*it) ){
            count++;
          }
          if( d_unk ){
            d_vars.push_back(*it);
          }
        }
        tests++;
      }
    }else if( d_testType==3 ){
      while( tests<totalTests ){
        for( Node v : f ){
          if( testVar(v) ){
            count++;
          }
          if( d_unk ){
            d_vars.push_back(v);
          }
        }
        tests++;
      }
    }else if( d_testType==4 ){
      while( tests<totalTests ){
        for( const Node& v : f ){
          if( testVar(v) ){
            count++;
          }
          if( d_unk ){
            d_vars.push_back(v);
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
          if( d_unk ){
            d_vars.push_back(v);
          }
        }
        tests++;
      }
    }else{
      std::stringstream ss;
      ss << "Unknown test type " << d_testType << " for count node test";
      Unhandled(ss.str());
    }
  }
  Trace("ajr-test") << "Count is " << count << std::endl;  
}

}
