#include "perf_tests.h"

namespace CVC4 {
  
void PerfTest::runTestCountDataStructures()
{
  Trace("ajr-test") << "----Test count (data structures)..." << std::endl;
  // do not resue terms
  initializeVars(d_depth, 1.0);
  // the find variable 
  Node fvar = d_vars[0];
  // shuffle
  std::random_shuffle( d_vars.begin(), d_vars.end() );
    
  long totalTests = double(d_totalTestsF)*1000000000.0/(double)(d_depth);
  Trace("ajr-test") << "---Total tests is " << totalTests << "..." << std::endl;
  long tests = 0;
  long count = 0;
  
  std::vector< Node > lvars;
  lvars.insert(lvars.end(),d_vars.begin(),d_vars.end());
  std::random_shuffle(lvars.begin(),lvars.end());
  
  if( d_testType==0 || d_testType==1 || d_testType==2 || d_testType==3 ){
    // maps
    std::map< Node, Node > vmap;
    for( unsigned i=0; i<lvars.size(); i++ ){
      vmap[d_vars[i]] = lvars[i];
    }
    if( d_testType==0 ){
      while( tests<totalTests ){
        for( std::map< Node, Node >::iterator it = vmap.begin(); it != vmap.end(); ++it ){
          if( it->first==fvar ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==1 ){
      while( tests<totalTests ){
        for( std::pair< Node, Node > v : vmap ){
          if( v.first==fvar ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==2 ){
      while( tests<totalTests ){
        for( const std::pair< Node, Node >& v : vmap ){
          if( v.first==fvar ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==3 ){
      while( tests<totalTests ){
        for( auto& v : vmap ){
          if( v.first==fvar ){
            count++;
          }
        }
        tests++;
      }
    }
  }else if( d_testType==4 || d_testType==5 || d_testType==6 || d_testType==7 ){
    // unordered maps
    std::unordered_map< Node, Node, NodeHashFunction > vmap;
    for( unsigned i=0; i<lvars.size(); i++ ){
      vmap[d_vars[i]] = lvars[i];
    }
    if( d_testType==4 ){
      while( tests<totalTests ){
        for( std::unordered_map< Node, Node, NodeHashFunction >::iterator it = vmap.begin(); it != vmap.end(); ++it ){
          if( it->first==fvar ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==5 ){
      while( tests<totalTests ){
        for( std::pair< Node, Node > v : vmap ){
          if( v.first==fvar ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==6 ){
      while( tests<totalTests ){
        for( const std::pair< Node, Node >& v : vmap ){
          if( v.first==fvar ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==7 ){
      while( tests<totalTests ){
        for( auto& v : vmap ){
          if( v.first==fvar ){
            count++;
          }
        }
        tests++;
      }
    }
  }else if( d_testType==8 || d_testType==9 || d_testType==10 || d_testType==11  ){
    // unordered maps
    std::unordered_set< Node, NodeHashFunction > vset;
    for( unsigned i=0; i<lvars.size(); i++ ){
      vset.insert( d_vars[i] );
    }
    if( d_testType==8 ){
      while( tests<totalTests ){
        for( std::unordered_set< Node, NodeHashFunction >::iterator it = vset.begin(); it != vset.end(); ++it ){
          if( *it==fvar ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==9 ){
      while( tests<totalTests ){
        for( Node v : vset ){
          if( v==fvar ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==10 ){
      while( tests<totalTests ){
        for( const Node& v : vset ){
          if( v==fvar ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==1 ){
      while( tests<totalTests ){
        for( auto& v : vset ){
          if( v==fvar ){
            count++;
          }
        }
        tests++;
      }
    }
  }else{
    std::stringstream ss;
    ss << "Unknown test type " << d_testType << " for count data structure test";
    Unhandled(ss.str());
  }
  Trace("ajr-test") << "Count is " << count << std::endl;  
}

}
