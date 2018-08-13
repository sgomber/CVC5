#include "theory/sample/theory_sample.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sample {

/** Constructs a new instance of TheorySample w.r.t. the provided contexts. */
TheorySample::TheorySample(context::Context* c,
                           context::UserContext* u,
                           OutputChannel& out,
                           Valuation valuation,
                           const LogicInfo& logicInfo) :
    Theory(THEORY_SAMPLE, c, u, out, valuation, logicInfo),
    d_not_elim(u),
    d_sample_checks(c)
    {
}/* TheorySample::TheorySample() */

void TheorySample::check(Effort level) {
  if (done() && level<EFFORT_FULL) {
    return;
  }
  TimerStat::CodeTimer checkTimer(d_checkTime);

  if( level==EFFORT_LAST_CALL )
  {
    return checkLastCall();
  }
  NodeManager * nm = NodeManager::currentNM();

  while(!done()) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Trace("sample-debug") << "TheorySample::check(): processing " << fact << std::endl;

    // Do the work
    switch(fact.getKind()) {
    case EQUAL:
      //do nothing
      break;
    case NOT:
      if( d_not_elim.find(fact)==d_not_elim.end() )
      {
        d_not_elim.insert(fact);
        if( fact[0].getKind()==SAMPLE_CHECK )
        {
          // not SAMPLE_CHECK( P ) ---> SAMPLE_CHECK( NOT P )
          Node redFact = nm->mkNode(SAMPLE_CHECK, fact[0][0].negate() );
          Node lem = fact.eqNode(redFact);
          Trace("sample-lemma") << "TheorySample::lemma : elim not : " << lem << std::endl;
          d_out->lemma(lem);
        }
      }
      break;
    case SAMPLE_CHECK:
      // add the sample check to the list of facts, we process these at last
      // call effort
      d_sample_checks.insert(fact);
      break;
    default:
      Unhandled(fact.getKind());
    }
  }

}/* TheorySample::check() */

bool TheorySample::needsCheckLastEffort() {
  return !d_sample_checks.empty();
}

void TheorySample::checkLastCall()
{
  std::vector< Node > asserts;
  Trace("sample-check") << "----- TheorySample::check" << std::endl;
  Trace("sample-check") << "Checking " << d_sample_checks.size() << " assertions : " << std::endl;
  for( NodeSet::const_iterator it = d_sample_checks.begin(); it != d_sample_checks.end(); ++it ){
    Trace("sample-check") << "  " << (*it) << std::endl;
    asserts.push_back( *it );
  }
}

}/* CVC4::theory::sample namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
