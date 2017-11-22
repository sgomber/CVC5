#include "perf_tests.h"

#include "options/smt_options.h"

namespace CVC4 {
  
void PerfTest::runTestCountVector()
{
  Trace("ajr-test") << "----Test count..." << std::endl;
  initializeVars(d_depth, d_rf);
    
  // 10^8 tests
  long totalTests = double(d_totalTestsF)*100000000.0/(double)(d_depth);
  Trace("ajr-test") << "---Total tests is " << totalTests << "..." << std::endl;
  long tests = 0;
  long count = 0;

  // 0 : counter over vector 
  // 1 : counter+size over vector 
  // 2 : iterator over vector 
  // 3 : range iterator over vector
  // 4 : const reference range iterator over vector
  // 5 : auto range iterator over vector
  Trace("ajr-test") << "----Test count vector..." << std::endl;
  if( !options::useUnknown() ){
    if( d_testType==0 ){
      while( tests<totalTests ){
        for( unsigned i=0; i<d_vars.size(); i++ ){
          if( testVar(d_vars[i]) ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==1 ){
      while( tests<totalTests ){
        for( unsigned i=0, size = d_vars.size(); i<size; i++ ){
          if( testVar(d_vars[i]) ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==2 ){
      while( tests<totalTests ){
        for( std::vector< Node >::iterator it = d_vars.begin(); it != d_vars.end(); ++it ){
          if( testVar(*it) ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==3 ){
      while( tests<totalTests ){
        for( Node v : d_vars ){
          if( testVar(v) ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==4 ){
      while( tests<totalTests ){
        for( Node& v : d_vars ){
          if( testVar(v) ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==5 ){
      while( tests<totalTests ){
        for( const Node& v : d_vars ){
          if( testVar(v) ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==6 ){
      while( tests<totalTests ){
        for( auto& v : d_vars ){
          if( testVar(v) ){
            count++;
          }
        }
        tests++;
      }
    }else if( d_testType==7 ){
      while( tests<totalTests ){
        for( auto v : d_vars ){
          if( testVar(v) ){
            count++;
          }
        }
        tests++;
      }

    }else if( d_testType==8 ){
      while( tests<totalTests ){
        for( const auto& v : d_vars ){
          if( testVar(v) ){
            count++;
          }
        }
        tests++;
      }

    }else if( d_testType==9 ){
      while( tests<totalTests ){
        for( const auto v : d_vars ){
          if( testVar(v) ){
            count++;
          }
        }
        tests++;
      }
    }else{
      std::stringstream ss;
      ss << "Unknown test type " << d_testType << " for count vector test";
      Unhandled(ss.str());
    }
  }else{
    if( d_testType==0 ){
      while( tests<totalTests ){
        for( unsigned i=0; i<d_vars.size(); i++ ){
          if( testVar(d_vars[i]) ){
            count++;
          }
          if( d_unk ){
            d_vars.push_back(d_vars[i]);
          }
        }
        tests++;
      }
    }else if( d_testType==1 ){
      while( tests<totalTests ){
        for( unsigned i=0, size = d_vars.size(); i<size; i++ ){
          if( testVar(d_vars[i]) ){
            count++;
          }
          if( d_unk ){
            d_vars.push_back(d_vars[i]);
          }
        }
        tests++;
      }
    }else if( d_testType==2 ){
      while( tests<totalTests ){
        for( std::vector< Node >::iterator it = d_vars.begin(); it != d_vars.end(); ++it ){
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
        for( Node v : d_vars ){
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
        for( Node& v : d_vars ){
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
        for( const Node& v : d_vars ){
          if( testVar(v) ){
            count++;
          }
          if( d_unk ){
            d_vars.push_back(v);
          }
        }
        tests++;
      }
    }else if( d_testType==6 ){
      while( tests<totalTests ){
        for( auto& v : d_vars ){
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
      ss << "Unknown test type " << d_testType << " for count vector test";
      Unhandled(ss.str());
    }
  }
  Trace("ajr-test") << "Count is " << count << std::endl;  
}

}
