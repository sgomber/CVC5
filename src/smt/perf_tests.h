
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
  void run();
private:
  void runTestFindDataStructures();
  void runTestCountVector();
  void runTestCountNode();
  void runTestCountDataStructures();
  
  double d_rf;
  unsigned d_depth;
  unsigned d_testType;
  unsigned d_totalTestsF;
  std::vector< Node > d_vars;
  bool d_unk;
  
  void initializeVars( unsigned use_depth, double use_rf);
  Node mkRandom(unsigned depth, double rf );
};

} 

#endif
