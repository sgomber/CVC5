#include "theory/sample/theory_sample.h"

#include "theory/theory_model.h"

#include "theory/sample/theory_sample_rewriter.h"
#include "options/sample_options.h"

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
  d_num_samples = options::numSamples();
  d_num_samples_sat = options::numSamplesSat();
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
      // if we need no samples to be SAT, we don't need to check
      if( d_num_samples_sat>0 )
      {
        // add the sample check to the list of facts, we process these at last
        // call effort
        registerSampleCheck(fact);
        d_sample_checks.insert(fact);
      }
      break;
    default:
      Unhandled(fact.getKind());
    }
  }

}/* TheorySample::check() */

void TheorySample::registerSampleCheck(Node n)
{
  if( d_ainfo.find(n)!=d_ainfo.end() )
  {
    return;
  }
  d_ainfo[n].init();
  AssertInfo& ai = d_ainfo[n];
  
  Assert( d_hasSample.find(n)==d_hasSample.end() );
  
  std::map< Node, bool >::iterator it;
  std::map<Node, bool, TNodeHashFunction>::iterator itc;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    it = d_hasSample.find(cur);
    // if we haven't computed whether there are sample terms in cur
    if( it==d_hasSample.end() )
    {
      d_hasSample[cur] = false;
      visit.push_back(cur);
      for( const Node& cc : cur ){
        visit.push_back(cc);
      }
    }else{
      bool hasSample = false;
      TypeNode ctn = cur.getType();
      if( TheorySampleRewriter::isSampleType(ctn) )
      {
        registerSampleType(ctn);
        d_isSample[cur] = true;
        hasSample = true;
      }
      if( !hasSample )
      {
        for (const Node& cn : cur) {
          // does the child have sampling?
          itc = d_hasSample.find(cn);
          if( itc->second )
          {
            hasSample = true;
            break;
          }
        }
      }
      d_hasSample[cur] = hasSample;
    }
  } while (!visit.empty());
  // should only check things with sampling in it
  Assert( d_hasSample[n] );
  
  // now, go top-down to collect (non-constant) free terms
  std::unordered_set<TNode, TNodeHashFunction> visited;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end()) {
      visited.insert(cur);
      if( !d_hasSample[cur] && !cur.isConst() )
      {
        ai.d_free_terms.push_back(cur);
      }
      else if( d_isSample.find(cur)!=d_isSample.end() )
      {
        ai.d_sample_terms.push_back(cur);
      }
      else
      {
        for (const Node& cn : cur ){
          visit.push_back(cn);
        }
      }
    }
  } while (!visit.empty());
}

void TheorySample::registerSampleType(TypeNode tn)
{
  // TODO
}

bool TheorySample::needsCheckLastEffort() {
  return !d_sample_checks.empty();
}

void TheorySample::checkLastCall()
{
  d_bmv.clear();
  std::vector< Node > asserts;
  Trace("sample-check") << "----- TheorySample::check" << std::endl;
  Trace("sample-check") << "Checking " << d_sample_checks.size() << " assertions : " << std::endl;
  for( NodeSet::const_iterator it = d_sample_checks.begin(); it != d_sample_checks.end(); ++it ){
    Node n = *it;
    Trace("sample-check") << "  " << n << std::endl;
    Node bmv = getBaseModelValue(n);
    bmv = Rewriter::rewrite(bmv);
    Trace("sample-check") << "  ...mv: " << bmv << std::endl;
    Trace("sample-check-debug") << "  ...free terms: " << d_ainfo[n].d_free_terms << std::endl;
    Trace("sample-check-debug") << "  ...sample terms: " << d_ainfo[n].d_sample_terms << std::endl;
    if( bmv.isConst() )
    {
      // TODO
    }
    else
    {
      asserts.push_back( bmv );
    }
  }
  Trace("sample-check") << "We have " << d_base_sample_terms.size() << " base sample terms : " << std::endl;
  std::map< Node, std::vector< Node > >::iterator itv;
  for( const Node& bst : d_base_sample_terms )
  {
    Trace("sample-check") << "  " << bst << std::endl;

    // compute its sample values
    itv = d_bst_to_values.find(bst);
    if( itv==d_bst_to_values.end() )
    {
      d_bst_to_values[bst].clear();
      itv = d_bst_to_values.find(bst);
      TypeNode tn = bst.getType();
      Assert( TheorySampleRewriter::isSampleType(tn) );
      for( unsigned i=0; i<d_num_samples; i++ )
      {
        Node sv = getSampleValue(tn);
        itv->second.push_back(sv);
      }
    }
  }
  // now, compute the value of the conjunction of asserts
  unsigned sat_count = 0;
  for( unsigned i=0; i<d_num_samples; i++ )
  {
    bool success = true;
    for( const Node& ba : asserts )
    {
      
    }
    if( success )
    {
      sat_count++;
    }
  }
}


Node TheorySample::getBaseModelValue(Node n)
{
  NodeManager * nm = NodeManager::currentNM();
  TheoryModel * tm = getValuation().getModel();
  std::unordered_map<Node, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    it = d_bmv.find(cur);

    if (it == d_bmv.end()) {
      if( !d_hasSample[cur] )
      {
        // just get the model value
        d_bmv[cur] = tm->getValue(cur);
      }
      else
      {
        d_bmv[cur] = Node::null();
        visit.push_back(cur);
        for (const Node& cn : cur) {
          visit.push_back(cn);
        }
      }
    } else if (it->second.isNull()) {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur) {
        it = d_bmv.find(cn);
        Assert(it != d_bmv.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged) 
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      d_bmv[cur] = ret;
      if( d_isSample.find(cur)!=d_isSample.end() )
      {
        d_base_sample_terms.push_back(ret);
      }
    }
  } while (!visit.empty());
  Assert(d_bmv.find(n) != d_bmv.end());
  Assert(!d_bmv.find(n)->second.isNull());
  return d_bmv[n];
}

Node TheorySample::getSampleValue(TypeNode tn)
{
  
  
  return Node::null();
}

}/* CVC4::theory::sample namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
