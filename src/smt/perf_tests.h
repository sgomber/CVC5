
#include "cvc4_private.h"

#ifndef __CVC4__PERF_TEST_H
#define __CVC4__PERF_TEST_H

#include <vector>
#include <stack>
#include <map>
#include <unordered_map>
#include <unordered_set>

#include "expr/node.h"

namespace CVC4 {
  
class PerfTest
{
public:
  PerfTest() : d_rf(0.0), d_depth(0), d_testFamily(0), d_testType(0), d_totalTestsF(0), d_mkVarCount(0), d_unk(false){}
  void run();
private:
  void runTestFindDataStructures();
  void runTestCountVector();
  void runTestCountNode();
  void runTestCountDataStructures();
  
  double d_rf;
  unsigned d_depth;
  unsigned d_testFamily;
  unsigned d_testType;
  unsigned d_totalTestsF;
  unsigned d_mkVarCount;
  std::vector< Node > d_vars;
  std::vector< TNode > d_tvars;
  Node d_test_var;
  std::unordered_set< Node, NodeHashFunction > d_vars_test;
  bool d_unk;
  
  void initializeVars( unsigned use_depth, double use_rf);
  Node mkVar();
  Node mkRandom(unsigned depth, double rf );
  //inline bool testVar( Node v ) { return d_vars_test.find(v)!=d_vars_test.end(); }
  inline bool testVar( Node v ) { return v>d_test_var; }
};

} 

#endif
