/*********************                                                        */
/*! \file ce_guided_instantiation.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief counterexample guided instantiation class
 **   This class is the entry point for both synthesis algorithms in Reynolds et al CAV 2015
 **
 **/
#include "theory/quantifiers/sygus/ce_guided_instantiation.h"

#include "options/quantifiers_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegInstantiation::CegInstantiation( QuantifiersEngine * qe, context::Context* c ) : QuantifiersModule( qe ),
d_master_conj(nullptr),
d_last_inst_si(false),
d_requested_dec(c,false){
  d_conjs.push_back(std::unique_ptr<CegConjecture>(new CegConjecture(qe)));
  d_master_conj = d_conjs[0].get();    
}

CegInstantiation::~CegInstantiation(){ 
}

bool CegInstantiation::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_LAST_CALL && !d_conj_quant.isNull();
}

QuantifiersModule::QEffort CegInstantiation::needsModel(Theory::Effort e)
{
  return d_master_conj->isSingleInvocation() ? QEFFORT_STANDARD : QEFFORT_MODEL;
}

void CegInstantiation::check(Theory::Effort e, QEffort quant_e)
{
  if( d_conj_quant.isNull() )
  {
    // not assigned, nothing to do
    return;
  }
  QEffort echeck = d_master_conj->isSingleInvocation() ? QEFFORT_STANDARD : QEFFORT_MODEL;
  if( quant_e!=echeck )
  {
    // must be at the correct effort level
    return;
  }
  Trace("cegqi-engine") << "---Counterexample Guided Instantiation Engine---" << std::endl;
  Trace("cegqi-engine-debug") << std::endl;
  bool active = false;
  bool value;
  if( d_quantEngine->getValuation().hasSatValue( d_conj_quant, value ) ) {
    active = value;
  }else{
    Trace("cegqi-engine-debug") << "...no value for quantified formula." << std::endl;
  }
  Trace("cegqi-engine-debug") << "Current conjecture status : active : " << active << std::endl;
  if( !active )
  {
    // if not active, we are done
    return;
  }
  // check each conjecture
  for( unsigned i=0,size=d_conjs.size(); i<size; i++ )
  {
    if( size>1 )
    {
      Trace("cegqi-engine") << "-----conjecture #" << i << "..." << std::endl;
    }
    if( d_conjs[i]->needsCheck() )
    {
      checkCegConjecture( d_conjs[i].get() );
    }
  }
  Trace("cegqi-engine") << "Finished Counterexample Guided Instantiation engine." << std::endl;
}

void CegInstantiation::registerQuantifier( Node q ) {
  if( d_quantEngine->getOwner( q )!=this ){
    Trace("cegqi-debug") << "Register quantifier : " << q << std::endl;
    return;
  }
  else if( !d_conj_quant.isNull() )
  {
    Assert(false);
    return;
  }
  Assert( q.getKind()==FORALL );
  d_conj_quant = q;
  Trace("cegqi") << "Register conjecture : " << q << std::endl;
  // is it a multi-conjecture?
  if( q[1].getKind()==AND )
  {
    NodeManager * nm = NodeManager::currentNM();
    // make the set of conjectures
    std::vector< Node > conjectures;
    std::vector< Node > cnames;
    std::vector< Node > qchildren;
    qchildren.push_back( q[0] );
    qchildren.push_back( Node::null() );
    if( q.getNumChildren()==3 )
    {
      qchildren.push_back( q[2] );
    }
    for( const Node& c : q[1] )
    {
      Assert( c.getKind()==NOT && c[0].getKind()==FORALL );
      QAttributes qa;
      QuantAttributes::computeQuantAttributes(c[0],qa);
      // remember the name
      Node cname = qa.d_name;
      // remove the name and rewrite
      Node cc = nm->mkNode( FORALL, c[0][0], c[0][1] );
      cc = Rewriter::rewrite( cc );
      // make the (miniscoped) conjecture
      qchildren[1] = cc.negate();
      Node conj = nm->mkNode( FORALL, qchildren );
      // add to vector
      cnames.push_back( cname );
      conjectures.push_back( conj );
      Trace("cegqi") << "...conjecture " << cname << " : " << conj << std::endl;
    }
    // make new conjectures
    for( unsigned i=1, size=conjectures.size(); i<size; i++ )
    {
      d_conjs.push_back(std::unique_ptr<CegConjecture>(new CegConjecture(d_quantEngine,d_master_conj)));
    }
    for( unsigned i=0, size=conjectures.size(); i<size; i++ )
    {
      // assign the conjecture
      d_conjs[i]->assign( conjectures[i] );
      // set the name of the conjecture
      d_conjs[i]->setName( cnames[i] );
    }
    //AlwaysAssert(false);
  }
  else
  {    
    // normal initialization
    d_master_conj->assign( q );
  }
}

Node CegInstantiation::getNextDecisionRequest( unsigned& priority ) {
  if( !d_master_conj->isAssigned() || d_requested_dec.get() )
  {
    // not yet initialized, or we've made all necessary decisions
    return Node::null();
  }
  for( unsigned i=0,size=d_conjs.size(); i<size; i++ )
  {
    Node dec_req = d_conjs[i]->getNextDecisionRequest( priority );
    if( !dec_req.isNull() )
    {
      Trace("cegqi-debug") << "CEGQI : Conjecture #" << i << " decide next on : " << dec_req << "..." << std::endl;
      return dec_req;
    }
  }
  Trace("cegqi-debug") << "...no decisions." << std::endl;
  // no more decisions will be made in this SAT context
  d_requested_dec.set(true);
  return Node::null();
}

void CegInstantiation::checkCegConjecture( CegConjecture * conj ) {
  if( Trace.isOn("cegqi-engine-debug") ){
    conj->debugPrint("cegqi-engine-debug");
    Trace("cegqi-engine-debug") << std::endl;
  }

  if( !conj->needsRefinement() ){
    Trace("cegqi-engine-debug") << "Do conjecture check..." << std::endl;
    if( conj->isSyntaxGuided() ){
      std::vector< Node > clems;
      conj->doSingleInvCheck( clems );
      if( !clems.empty() ){
        d_last_inst_si = true;
        for( unsigned j=0; j<clems.size(); j++ ){
          Trace("cegqi-lemma") << "Cegqi::Lemma : single invocation instantiation : " << clems[j] << std::endl;
          d_quantEngine->addLemma( clems[j] );
        }
        d_statistics.d_cegqi_si_lemmas += clems.size();
        Trace("cegqi-engine") << "  ...try single invocation." << std::endl;
        return;
      }
      
      Trace("cegqi-engine") << "  *** Check candidate phase..." << std::endl;
      std::vector< Node > cclems;
      conj->doCheck(cclems);
      bool addedLemma = false;
      for( unsigned i=0; i<cclems.size(); i++ ){
        Node lem = cclems[i];
        d_last_inst_si = false;
        Trace("cegqi-lemma") << "Cegqi::Lemma : check : " << lem << std::endl;
        if( d_quantEngine->addLemma( lem ) ){
          ++(d_statistics.d_cegqi_lemmas_ce);
          addedLemma = true;
        }else{
          //this may happen if we eagerly unfold, simplify to true
          if( !options::sygusDirectEval() ){
            Trace("cegqi-warn") << "  ...FAILED to add check lemma!" << std::endl;
          }else{
            Trace("cegqi-engine-debug") << "  ...FAILED to add check lemma!" << std::endl;
          }
        }
      }
      if( addedLemma ){
        Trace("cegqi-engine") << "  ...added check lemma." << std::endl;
      }else{
        Trace("cegqi-engine") << "  ...did not add check lemma." << std::endl;
        if( conj->needsRefinement() ){
          //immediately go to refine candidate
          checkCegConjecture( conj );
          return;
        }
      } 
    }else{
      Trace("cegqi-engine") << "  *** Check candidate phase (non-SyGuS)." << std::endl;
      std::vector< Node > lems;
      conj->doBasicCheck(lems);
      Assert(lems.empty());
    }
  }else{
    Trace("cegqi-engine") << "  *** Refine candidate phase..." << std::endl;
    std::vector< Node > rlems;
    conj->doRefine( rlems );
    bool addedLemma = false;
    for( unsigned i=0; i<rlems.size(); i++ ){
      Node lem = rlems[i];
      Trace("cegqi-lemma") << "Cegqi::Lemma : refinement : " << lem << std::endl;
      bool res = d_quantEngine->addLemma( lem );
      if( res ){
        ++(d_statistics.d_cegqi_lemmas_refine);
        conj->incrementRefineCount();
        addedLemma = true;
      }else{
        Trace("cegqi-warn") << "  ...FAILED to add refine lemma!" << std::endl;
      }
    }
    if( addedLemma ){
      Trace("cegqi-engine") << "  ...added refine lemma." << std::endl;
    }else{
      Trace("cegqi-engine") << "  ...did not add refine lemma." << std::endl;
      if( !conj->needsRefinement() )
      {
        //immediately go to check candidate
        checkCegConjecture( conj );
        return;
      }
    }
  }
}

void CegInstantiation::printSynthSolution( std::ostream& out ) {
  if( d_master_conj->isAssigned() )
  {
    d_master_conj->printSynthSolution( out, d_last_inst_si );
  }
  else
  {
    Assert( false );
  }
}

void CegInstantiation::getSynthSolutions(std::map<Node, Node>& sol_map)
{
  if (d_master_conj->isAssigned())
  {
    d_master_conj->getSynthSolutions(sol_map, d_last_inst_si);
  }
  else
  {
    Assert(false);
  }
}

void CegInstantiation::preregisterAssertion( Node n ) {
  //check if it sygus conjecture
  if( QuantAttributes::checkSygusConjecture( n ) ){
    //this is a sygus conjecture
    Trace("cegqi") << "Preregister sygus conjecture : " << n << std::endl;
    d_master_conj->preregisterConjecture( n );
  }
}

CegInstantiation::Statistics::Statistics()
    : d_cegqi_lemmas_ce("CegInstantiation::cegqi_lemmas_ce", 0),
      d_cegqi_lemmas_refine("CegInstantiation::cegqi_lemmas_refine", 0),
      d_cegqi_si_lemmas("CegInstantiation::cegqi_lemmas_si", 0),
      d_solutions("CegConjecture::solutions", 0),
      d_candidate_rewrites_print("CegConjecture::candidate_rewrites_print", 0),
      d_candidate_rewrites("CegConjecture::candidate_rewrites", 0)

{
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->registerStat(&d_cegqi_si_lemmas);
  smtStatisticsRegistry()->registerStat(&d_solutions);
  smtStatisticsRegistry()->registerStat(&d_candidate_rewrites_print);
  smtStatisticsRegistry()->registerStat(&d_candidate_rewrites);
}

CegInstantiation::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_si_lemmas);
  smtStatisticsRegistry()->unregisterStat(&d_solutions);
  smtStatisticsRegistry()->unregisterStat(&d_candidate_rewrites_print);
  smtStatisticsRegistry()->unregisterStat(&d_candidate_rewrites);
}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
