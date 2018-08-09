#include "theory/sample/theory_sample.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace sample {

/** Constructs a new instance of TheorySample w.r.t. the provided contexts. */
TheorySample::TheorySample(context::Context* c,
                           context::UserContext* u,
                           OutputChannel& out,
                           Valuation valuation,
                           const LogicInfo& logicInfo) :
    Theory(THEORY_SAMPLE, c, u, out, valuation, logicInfo) {
}/* TheorySample::TheorySample() */

void TheorySample::check(Effort level) {
  if (done() && !fullEffort(level)) {
    return;
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);

  while(!done()) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Debug("sample") << "TheorySample::check(): processing " << fact << std::endl;

    // Do the work
    switch(fact.getKind()) {

    /* cases for all the theory's kinds go here... */

    default:
      Unhandled(fact.getKind());
    }
  }

}/* TheorySample::check() */

}/* CVC4::theory::sample namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
