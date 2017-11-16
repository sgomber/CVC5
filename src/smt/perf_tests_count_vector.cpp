#include "perf_tests.h"

namespace CVC4 {
  
void PerfTest::runTestCountVector()
{
  Trace("ajr-test") << "----Test count..." << std::endl;
  initializeVars(d_depth, d_rf);
  // the find variable 
  Node fvar = d_vars[0];
  // shuffle
  std::random_shuffle( d_vars.begin(), d_vars.end() );
    
  long totalTests = double(d_totalTestsF)*1000000000.0/(double)(d_depth);
  Trace("ajr-test") << "---Total tests is " << totalTests << "..." << std::endl;
  long tests = 0;
  long count = 0;

  // 0 : counter over vector 
  // 1 : counter+size over vector 
  // 2 : iterator over vector 
  // 3 : range iterator over vector
  // 4 : counter over vector with unknown
  // 5 : counter+size over vector with unknown
  // 6 : iterator over vector with unknown
  // 7 : range iterator over vector with unknown
  Trace("ajr-test") << "----Test count..." << std::endl;
  if( d_testType==0 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<d_vars.size(); i++ ){
        if( d_vars[i]==fvar ){
          count++;
        }
      }
      tests++;
    }
  }else if( d_testType==1 ){
    while( tests<totalTests ){
      for( unsigned i=0, size = d_vars.size(); i<size; i++ ){
        if( d_vars[i]==fvar ){
          count++;
        }
      }
      tests++;
    }
  }else if( d_testType==2 ){
    while( tests<totalTests ){
      for( std::vector< Node >::iterator it = d_vars.begin(); it != d_vars.end(); ++it ){
        if( *it==fvar ){
          count++;
        }
      }
      tests++;
    }
  }else if( d_testType==3 ){
    while( tests<totalTests ){
      for( Node v : d_vars ){
        if( v==fvar ){
          count++;
        }
      }
      tests++;
    }
  }else if( d_testType==4 ){
    while( tests<totalTests ){
      for( unsigned i=0; i<d_vars.size(); i++ ){
        if( d_vars[i]==fvar ){
          count++;
        }
        if( d_unk ){
          d_vars.push_back(fvar);
        }
      }
      tests++;
    }
  }else if( d_testType==5 ){
    while( tests<totalTests ){
      for( unsigned i=0, size = d_vars.size(); i<size; i++ ){
        if( d_vars[i]==fvar ){
          count++;
        }
        if( d_unk ){
          d_vars.push_back(fvar);
        }
      }
      tests++;
    }
  }else if( d_testType==6 ){
    while( tests<totalTests ){
      for( std::vector< Node >::iterator it = d_vars.begin(); it != d_vars.end(); ++it ){
        if( *it==fvar ){
          count++;
        }
        if( d_unk ){
          d_vars.push_back(fvar);
        }
      }
      tests++;
    }
  }else if( d_testType==7 ){
    while( tests<totalTests ){
      for( Node v : d_vars ){
        if( v==fvar ){
          count++;
        }
        if( d_unk ){
          d_vars.push_back(fvar);
        }
      }
      tests++;
    }
  }else{
    std::stringstream ss;
    ss << "Unknown test type " << d_testType << " for count vector test";
    Unhandled(ss.str());
  }
  Trace("ajr-test") << "Count is " << count << std::endl;  
}

}
