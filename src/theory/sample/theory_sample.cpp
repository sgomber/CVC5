#include "theory/sample/theory_sample.h"

#include "theory/theory_model.h"

#include "options/sample_options.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers_engine.h"
#include "theory/sample/theory_sample_rewriter.h"
#include "util/random.h"

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
                           const LogicInfo& logicInfo)
    : Theory(THEORY_SAMPLE, c, u, out, valuation, logicInfo),
      d_not_elim(u),
      d_sample_checks(c),
      d_num_samples(0),
      d_num_samples_nsat(0)
{
  d_rmax = Rational(LONG_MAX);
  d_true = NodeManager::currentNM()->mkConst(true);
}

void TheorySample::finishInit()
{
  d_num_samples = options::numSamples();
  unsigned num_samples_sat = options::numSamplesSat();
  if (num_samples_sat > d_num_samples)
  {
    d_num_samples_nsat = 0;
    // must have more samples than SAT samples
    std::stringstream ss;
    ss << "The number of SAT samples cannot be greater than the number of "
          "total samples: "
       << num_samples_sat << " SAT samples, " << d_num_samples
       << " total samples were indicated.";
    throw LogicException(ss.str());
  }
  else
  {
    d_num_samples_nsat = d_num_samples - num_samples_sat;
  }
}

void TheorySample::check(Effort level)
{
  if (done() && level < EFFORT_FULL)
  {
    return;
  }
  TimerStat::CodeTimer checkTimer(d_checkTime);

  if (level == EFFORT_LAST_CALL)
  {
    // call the last call effort check
    return checkLastCall();
  }
  NodeManager* nm = NodeManager::currentNM();

  while (!done())
  {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Trace("sample-debug") << "TheorySample::check(): processing " << fact
                          << std::endl;

    // Do the work
    switch (fact.getKind())
    {
      case EQUAL:
        // do nothing
        break;
      case NOT:
        if (d_not_elim.find(fact) == d_not_elim.end())
        {
          d_not_elim.insert(fact);
          if (fact[0].getKind() == SAMPLE_CHECK)
          {
            // not SAMPLE_CHECK( P ) ---> SAMPLE_CHECK( NOT P )
            Node redFact = nm->mkNode(SAMPLE_CHECK, fact[0][0].negate());
            Node lem = fact.eqNode(redFact);
            Trace("sample-lemma")
                << "TheorySample::lemma : elim not : " << lem << std::endl;
            d_out->lemma(lem);
          }
        }
        break;
      case SAMPLE_CHECK:
        // if we need no samples to be SAT, we don't need to check
        // if(d_num_samples==d_num_samples_nsat )
        //{
        // add the sample check to the list of facts, we process these at last
        // call effort
        registerSampleCheck(fact);
        d_sample_checks.insert(fact);
        //}
        break;
      default: Unhandled(fact.getKind());
    }
  }

} /* TheorySample::check() */

void TheorySample::registerSampleCheck(Node n)
{
  if (d_ainfo.find(n) != d_ainfo.end())
  {
    return;
  }
  d_ainfo[n].init();
  AssertInfo& ai = d_ainfo[n];

  Assert(d_hasSample.find(n) == d_hasSample.end());

  std::map<Node, bool>::iterator it;
  std::map<Node, bool, TNodeHashFunction>::iterator itc;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_hasSample.find(cur);
    // if we haven't computed whether there are sample terms in cur
    if (it == d_hasSample.end())
    {
      d_hasSample[cur] = false;
      visit.push_back(cur);
      for (const Node& cc : cur)
      {
        visit.push_back(cc);
      }
    }
    else
    {
      bool hasSample = false;
      TypeNode ctn = cur.getType();
      if (TheorySampleRewriter::isSampleType(ctn))
      {
        registerSampleType(ctn);
        hasSample = true;
      }
      if( cur.getKind()==SAMPLE_RUN )
      {
        d_isSample[cur] = true;
      }
      if (!hasSample)
      {
        for (const Node& cn : cur)
        {
          // does the child have sampling?
          itc = d_hasSample.find(cn);
          if (itc->second)
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
  Assert(d_hasSample[n]);

  // now, go top-down to collect (non-constant) free terms
  std::unordered_set<TNode, TNodeHashFunction> visited;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (!d_hasSample[cur] && !cur.isConst())
      {
        ai.d_free_terms.push_back(cur);
      }
      else if (d_isSample.find(cur) != d_isSample.end())
      {
        ai.d_sample_terms.push_back(cur);
        ai.d_sample_term_types.push_back(cur.getType());
      }
      else
      {
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
  } while (!visit.empty());
}

void TheorySample::registerSampleType(TypeNode tn)
{
  if (d_tinfo.find(tn) != d_tinfo.end())
  {
    return;
  }
  d_tinfo[tn].init();
  Trace("sample-type") << "Initialize sample type : " << tn << std::endl;
  TypeInfo& ti = d_tinfo[tn];
  Assert(TheorySampleRewriter::isSampleType(tn));

  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  ti.d_ncons = dt.getNumConstructors();
  bool valueValid = true;
  for (unsigned i = 0; i < ti.d_ncons; i++)
  {
    Trace("sample-type") << "Constructor #" << i << std::endl;
    Node op = Node::fromExpr(dt[i].getSygusOp());
    Trace("sample-type") << "  operator " << op << std::endl;
    ti.d_ops.push_back(op);
    Kind ok = UNDEFINED_KIND;
    if (op.getKind() == BUILTIN)
    {
      ti.d_builtin.push_back(true);
      ok = NodeManager::operatorToKind(op);
      Trace("sample-type") << "  builtin, kind : " << ok << std::endl;
    }
    else
    {
      ti.d_builtin.push_back(false);
      ok = datatypes::DatatypesRewriter::getOperatorKindForSygusBuiltin(op);
      Trace("sample-type") << "  non-builtin, app-kind : " << ok << std::endl;
    }
    ti.d_kinds.push_back(ok);
    std::vector<TypeNode> args;
    for (unsigned j = 0, nargs = dt[i].getNumArgs(); j < nargs; j++)
    {
      TypeNode at = TypeNode::fromType(dt[i].getArgType(j));
      args.push_back(at);
      // also register the subfield type
      registerSampleType(at);
    }
    Trace("sample-type") << "  #args=" << args.size() << std::endl;
    // is it a value?
    if (args.empty() && op.isConst())
    {
      if (valueValid)
      {
        if (ti.d_value.isNull())
        {
          ti.d_value = op;
        }
        else
        {
          ti.d_value = Node::null();
          valueValid = false;
        }
      }
    }
    else
    {
      valueValid = false;
    }
    unsigned rbounds[2] = {0, 0};
    if (ok == SAMPLE_INT_UNIF)
    {
      Assert(args.size() == 2);
      bool success = true;
      // check if we can avoid full precision rationals
      for (unsigned i = 0; i < 2; i++)
      {
        success = false;
        TypeNode at = args[i];
        Assert(d_tinfo.find(at) != d_tinfo.end());
        TypeInfo& ati = d_tinfo[at];
        if (!ati.d_value.isNull())
        {
          Assert(ati.d_value.isConst());
          Rational rv = ati.d_value.getConst<Rational>();
          if (rv < d_rmax)
          {
            rbounds[i] = rv.getNumerator().toUnsignedInt();
            success = true;
          }
        }
        if (!success)
        {
          // clean up
          rbounds[0] = 0;
          break;
        }
      }
      if (success)
      {
        Trace("sample-type")
            << tn << " is " << ok << ", small bounds: [" << rbounds[0] << ", "
            << rbounds[1] << "]" << std::endl;
        args.clear();
      }
    }
    ti.d_args.push_back(args);
    ti.d_rmin.push_back(rbounds[0]);
    ti.d_rmax.push_back(rbounds[1]);
  }
}

bool TheorySample::needsCheckLastEffort() { return !d_sample_checks.empty(); }

void TheorySample::checkLastCall()
{
  Trace("sample-check") << "----- TheorySample::check" << std::endl;
  bool success = runCheck();
  if (success)
  {
    Trace("sample-check") << "...no conflict" << std::endl;
    return;
  }
  // conflict
  // get the master equality engine
  d_masterEe = getQuantifiersEngine()->getMasterEqualityEngine();
  std::vector<Node> cvec;
  Trace("sample-check-debug") << "...make conflict : " << std::endl;
  // also must explain model value equalities
  for (const Node& ca : d_conflict)
  {
    cvec.push_back(ca.negate());
    Trace("sample-check-debug") << "  " << ca << std::endl;
    AssertInfo& cai = d_ainfo[ca];
    for (const Node& ft : cai.d_free_terms)
    {
      explainModelValue(ft, cvec);
    }
  }
  Node conflictNode =
      cvec.size() == 1 ? cvec[0] : NodeManager::currentNM()->mkNode(OR, cvec);
  Trace("sample-lemma") << "TheorySample::lemma : conflict : " << conflictNode
                        << std::endl;
  d_out->lemma(conflictNode);
}

Node TheorySample::explainModelValue(Node n, std::vector<Node>& exp)
{
  if (n.isConst())
  {
    return n;
  }

  Node mn = getValuation().getModel()->getValue(n);
  Node trivialExp = n.eqNode(mn).negate();

  // if we don't have the model value, its already hopeless
  if (d_masterEe->hasTerm(mn))
  {
    // does the master equality engine know about this term?
    if (d_masterEe->hasTerm(n))
    {
      // if so, the explanation is simple
      exp.push_back(trivialExp);
      return mn;
    }
    // otherwise, let's look at the children
    std::vector<Node> childrenExp;
    std::vector<Node> children;
    bool childChanged = false;
    bool success = true;
    for (const Node& nc : n)
    {
      Node ncv = explainModelValue(nc, childrenExp);
      if (ncv.isNull())
      {
        success = false;
        break;
      }
      children.push_back(ncv);
      childChanged = childChanged || ncv != nc;
    }
    if (success && childChanged)
    {
      if (n.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.insert(children.begin(), n.getOperator());
      }
      Node n2 = NodeManager::currentNM()->mkNode(n.getKind(), children);
      // does the master equality engine know about the modified term?
      if (d_masterEe->hasTerm(n2))
      {
        // properly explained it, using the children
        exp.insert(exp.end(), childrenExp.begin(), childrenExp.end());
        exp.push_back(n2.eqNode(mn).negate());
        return mn;
      }
    }
  }
  // can't explain it, just do model value equality
  exp.push_back(trivialExp);

  // if the type is finite, we are okay
  if (n.getType().isInterpretedFinite())
  {
    return mn;
  }
  Trace("sample-warn") << "TheorySample: WARNING: cannot explain model value "
                       << mn << " for " << n << std::endl;
  return Node::null();
}

bool TheorySample::runCheck()
{
  d_asserts.clear();
  d_basserts.clear();
  d_assert_to_value.clear();
  d_bmv.clear();
  d_base_sample_terms.clear();
  d_conflict.clear();

  std::map<Node, unsigned> ba_to_index;
  Trace("sample-check") << "Checking " << d_sample_checks.size()
                        << " assertions : " << std::endl;
  for (NodeSet::const_iterator it = d_sample_checks.begin();
       it != d_sample_checks.end();
       ++it)
  {
    Node n = *it;
    Trace("sample-check") << "  (" << d_asserts.size() << ") " << n
                          << std::endl;
    Node bmv = getBaseModelValue(n[0]);
    bmv = Rewriter::rewrite(bmv);
    Trace("sample-check") << "  ...mv: " << bmv << std::endl;
    Trace("sample-check-debug")
        << "  ...free terms: " << d_ainfo[n].d_free_terms << std::endl;
    Trace("sample-check-debug")
        << "  ...sample terms: " << d_ainfo[n].d_sample_terms << std::endl;
    if (bmv.isConst())
    {
      if (!bmv.getConst<bool>())
      {
        d_conflict.insert(n);
        return false;
      }
    }
    else
    {
      std::map<Node, unsigned>::iterator itbi = ba_to_index.find(bmv);
      if (itbi != ba_to_index.end())
      {
        // if we get a duplicate, we choose the assertion based on node ordering
        Node dupAssert = d_asserts[itbi->second];
        if (n < dupAssert)
        {
          d_asserts[itbi->second] = n;
        }
      }
      else
      {
        ba_to_index[bmv] = d_asserts.size();
        d_asserts.push_back(n);
        d_basserts.push_back(bmv);
      }
    }
  }
  if( Trace.isOn("sample-check") )
  {
    Trace("sample-check") << "We have " << d_base_sample_terms.size()
                          << " base sample terms : " << std::endl;
    //std::map<Node, std::vector<Node> >::iterator itv;
    for (const Node& bst : d_base_sample_terms)
    {
      Trace("sample-check") << "  " << bst << std::endl;
    }
  }
  // now, compute the value of the conjunction of d_asserts
  std::map<Node, std::vector<Node> > base_term_var_map;
  std::map<Node, std::vector<Node> > base_term_sub_map;
  for (const Node& a : d_asserts)
  {
    AssertInfo& ai = d_ainfo[a];
    std::vector<Node>& vars = base_term_var_map[a];
    std::vector<Node>& subs = base_term_sub_map[a];
    for (const Node& bast : ai.d_sample_terms)
    {
      Node st = d_bmv[bast];
      vars.push_back(st);
      subs.push_back(st[0]);
    }
  }

  // the valuation of d_asserts on each sample point
  unsigned nsat_count = 0;
  std::map< Node, Node >::iterator itbvi;
  TheoryModel * tm = getValuation().getModel();
  Trace("sample-check-pt") << "Check samples..." << std::endl;
  for (unsigned i = 0; i < d_num_samples; i++)
  {
    Trace("sample-check-pt") << "  Point #" << i << " : ";
    std::map<Node, Node>& btvi = d_bst_to_terms[i];
    bool success = true;
    Node baSubs;
    for (unsigned k = 0, size = d_asserts.size(); k < size; k++)
    {
      Node a = d_asserts[k];
      Node ba = d_basserts[k];
      std::vector<Node>& bt_vars = base_term_var_map[a];
      std::vector<Node>& bt_subs = base_term_sub_map[a];
      for (unsigned j = 0, nvars = bt_vars.size(); j < nvars; j++)
      {
        Node var = bt_vars[j];
        Node sub;
        itbvi = btvi.find(var);
        if( itbvi==btvi.end() )
        {
          Trace("sample-check-debug2") << "mkSampleValue " << i << " for " << var[0] << std::endl;
          sub = mkSampleValue(var[0].getType());
          Trace("sample-check-debug2") << "...got " << sub << std::endl;
          // cache the sample value
          d_bst_to_terms[i][var] = sub;
        }
        else
        {
          sub = itbvi->second;
        }
        // if not constant, consult the model value
        if( !sub.isConst() )
        {
          Trace("sample-check-debug2") << "Get model value for " << sub << std::endl;
          sub = tm->getValue(sub);
          Trace("sample-check-debug2") << "...got " << sub << std::endl;
        }
        bt_subs[j] = sub;
      }
      Trace("sample-check-debug2") << "In " << ba << std::endl;
      Trace("sample-check-debug2") << "Substitute : " << bt_vars << " -> " << bt_subs << std::endl;
      Node baSubs = ba.substitute(
          bt_vars.begin(), bt_vars.end(), bt_subs.begin(), bt_subs.end());
      Trace("sample-check-debug2") << "...got " << baSubs << std::endl;
      baSubs = Rewriter::rewrite(baSubs);
      d_assert_to_value[a][k] = baSubs;
      Assert(baSubs.isConst());
      Trace("sample-check-pt") << baSubs << " ";
      if (baSubs != d_true)
      {
        d_conflict.insert(a);
        success = false;
        break;
      }
    }
    Trace("sample-check-pt") << std::endl;
    if (!success)
    {
      nsat_count++;
      if (nsat_count > d_num_samples_nsat)
      {
        // conflict
        return false;
      }
    }
  }
  return true;
}

Node TheorySample::getBaseModelValue(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  TheoryModel* tm = getValuation().getModel();
  std::unordered_map<Node, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_bmv.find(cur);

    if (it == d_bmv.end())
    {
      if (!d_hasSample[cur])
      {
        // just get the model value
        d_bmv[cur] = tm->getValue(cur);
      }
      else
      {
        d_bmv[cur] = Node::null();
        visit.push_back(cur);
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
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
      if (d_isSample.find(cur) != d_isSample.end())
      {
        d_base_sample_terms.push_back(ret);
      }
    }
  } while (!visit.empty());
  Assert(d_bmv.find(n) != d_bmv.end());
  Assert(!d_bmv.find(n)->second.isNull());
  return d_bmv[n];
}

Node TheorySample::mkSampleValue(TypeNode tn)
{
  Assert(d_tinfo.find(tn) != d_tinfo.end());
  TypeInfo& ti = d_tinfo[tn];
  if (!ti.d_value.isNull())
  {
    return ti.d_value;
  }
  Assert(ti.d_ncons > 0);
  // get a random constructor index
  uint64_t opIndex = Random::getRandom().pick(0, ti.d_ncons - 1);
  // get the information
  Node op = ti.d_ops[opIndex];
  bool isBuiltin = ti.d_builtin[opIndex];
  std::vector<TypeNode>& argts = ti.d_args[opIndex];
  std::vector<Node> children;
  if (!isBuiltin)
  {
    children.push_back(op);
  }
  for (unsigned i = 0, nargs = argts.size(); i < nargs; i++)
  {
    Node asv = mkSampleValue(argts[i]);
    children.push_back(asv);
  }
  Kind ok = ti.d_kinds[opIndex];
  Node ret;
  if (isBuiltin)
  {
    if (ok == SAMPLE_INT_UNIF)
    {
      if (!children.empty())
      {
        // using full precision rationals
      }
      else
      {
        unsigned rmin = ti.d_rmin[opIndex];
        unsigned rmax = ti.d_rmax[opIndex];
        uint64_t rvalue =
            rmax > rmin ? Random::getRandom().pick(rmin, rmax) : rmin;
        ret = NodeManager::currentNM()->mkConst(Rational(rvalue));
      }
    }
    else
    {
      ret = NodeManager::currentNM()->mkNode(op, children);
    }
  }
  else if (children.size() == 1 && ok == UNDEFINED_KIND)
  {
    ret = children[0];
  }
  else
  {
    ret = NodeManager::currentNM()->mkNode(ok, children);
  }
  Assert(!ret.isNull());
  ret = Rewriter::rewrite(ret);
  return ret;
}

}  // namespace sample
}  // namespace theory
}  // namespace CVC4
