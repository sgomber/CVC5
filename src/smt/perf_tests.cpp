#include "perf_tests.h"

#include "options/smt_options.h"

namespace CVC4 {
  
void PerfTest::run()
{
  d_depth = options::testDepth();  
  Trace("ajr-test") << "Test depth is " << d_depth << "..." << std::endl;
  d_testType = options::testType();
  Trace("ajr-test") << "Test type is " << d_testType << "..." << std::endl;
  d_totalTestsF = options::totalTests()>1 ? options::totalTests() : 1;
  Trace("ajr-test") << "Test factor is " << d_totalTestsF << "..." << std::endl;
  d_rf = double(1.0)/double(options::testTermReuseFreq());
  Trace("ajr-test") << "Term reuse factor is " << (1.0-d_rf) << "..." << std::endl;
  
  // should be unknown but always false
  d_unk = options::dummyUnknown();
  
  d_testFamily = options::testFamily();
  
  if( d_testFamily==0 ){
    runTestFindDataStructures();
  }else if( d_testFamily==1 ){
    runTestCountVector();
  }else if( d_testFamily==2 ){
    runTestCountNode();
  }else if( d_testFamily>=3 && d_testFamily<=5 ){
    runTestCountDataStructures();
  }else{
    std::stringstream ss;
    ss << "Unknown test family " << d_testFamily;
    Unhandled(ss.str());
  }
}

Node PerfTest::mkVar() {
  std::stringstream ss;
  ss << "t" << d_mkVarCount;
  Node v = NodeManager::currentNM()->mkBoundVar( ss.str(), NodeManager::currentNM()->realType() );
  if( d_mkVarCount%2==0 ){
    d_vars_test.insert(v);
  }
  d_mkVarCount++;
  return v;
}
  
void PerfTest::initializeVars( unsigned use_depth, double use_rf ) {
  for( unsigned i=0; i<use_depth; i++ ){
    double r = (double)(rand())/((double)(RAND_MAX));
    if( r<use_rf || d_vars.empty() ){
      Node v = mkVar();
      d_vars.push_back( v );
    }else{
      r = (double)(rand())/((double)(RAND_MAX));
      unsigned iuse = (unsigned)( (double(d_vars.size())*r ) );
      if( iuse>=d_vars.size() ){
        iuse = d_vars.size()-1;        
      }
      d_vars.push_back(d_vars[iuse]);
    }
  }
  double r = (double)(rand())/((double)(RAND_MAX));
  unsigned iuse = (unsigned)( (double(d_vars.size())*r ) );
  if( iuse>=d_vars.size() ){
    iuse = d_vars.size()-1;        
  }
  d_test_var = d_vars[iuse];
  // shuffle
  std::random_shuffle( d_vars.begin(), d_vars.end() );
}

Node PerfTest::mkRandom(unsigned depth, double rf ){
  if( depth==0 ){
    double r = (double)(rand())/((double)(RAND_MAX));
    unsigned iuse;
    if( r<rf || d_vars.empty() ){
      iuse = d_vars.size();
      std::stringstream ss;
      ss << "t" << d_vars.size();
      Node v = mkVar();
      d_vars.push_back( v );
    }else{
      r = (double)(rand())/((double)(RAND_MAX));
      iuse = (unsigned)( (double(d_vars.size())*r ) );
      if( iuse>=d_vars.size() ){
        iuse = d_vars.size()-1;        
      }
    }
    Node v = d_vars[iuse];
    return v;
  }else{
    std::vector< Node > children;
    for( unsigned i=0; i<2; i++ ){
      Node c = mkRandom( depth-1, rf );
      children.push_back( c );
    }
    return NodeManager::currentNM()->mkNode( kind::PLUS, children );
  }
}

}
