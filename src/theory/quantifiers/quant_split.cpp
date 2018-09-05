/*********************                                                        */
/*! \file quant_split.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of dynamic quantifiers splitting
 **/

#include "theory/quantifiers/quant_split.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

QuantDSplit::QuantDSplit(QuantifiersEngine* qe)
    : QuantifiersModule(qe), d_reduced(qe->getUserContext())
{
}

void QuantDSplit::checkOwnership(Node q)
{
  Trace("quant-dsplit-debug") << "Check split quantified formula : " << q << std::endl;
  if (q.getNumChildren() == 3)
  {
    if (d_quantEngine->getQuantAttributes()->isQuantExpand(q))
    {
      // we expand here, since we need to be informed immediately if the
      // expansion is invalid.
      Node exq = expand(q);
      if (!exq.isNull())
      {
        Trace("quant-dsplit-debug") << "...will expand." << std::endl;
        d_quant_to_expanded[q] = exq;
        d_to_reduce.insert(q);
        d_quantEngine->setOwner(q, this);
        return;
      }
    }
  }
  unsigned max_index;
  int max_score = -1;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    TypeNode tn = q[0][i].getType();
    if( tn.isDatatype() ){
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      if( dt.isRecursiveSingleton( tn.toType() ) ){
        Trace("quant-dsplit-debug") << "Datatype " << dt.getName() << " is recursive singleton." << std::endl;
      }else{
        int score = -1;
        if( options::quantDynamicSplit()==quantifiers::QUANT_DSPLIT_MODE_AGG ){
          score = dt.isInterpretedFinite( tn.toType() ) ? 1 : 0;
        }else if( options::quantDynamicSplit()==quantifiers::QUANT_DSPLIT_MODE_DEFAULT ){
          //only split if goes from being unhandled -> handled by finite instantiation
          //  an example is datatypes with uninterpreted sort fields, which are "interpreted finite" but not "finite"
          if( !d_quantEngine->isFiniteBound( q, q[0][i] ) ){
            score = dt.isInterpretedFinite( tn.toType() ) ? 1 : -1;
          }
        }
        Trace("quant-dsplit-debug") << "Datatype " << dt.getName() << " is score " << score << " (" << dt.isInterpretedFinite( tn.toType() ) << " " << dt.isFinite( tn.toType() ) << ")" << std::endl;
        if( score>max_score ){
          max_index = i;
          max_score = score;
        }
      }
    }
  }

  if (max_score != -1)
  {
    Trace("quant-dsplit-debug")
        << "...will split at index " << max_index << "." << std::endl;
    d_quant_to_split[q] = max_index;
    d_to_reduce.insert(q);
    d_quantEngine->setOwner( q, this );
  }
}

/* whether this module needs to check this round */
bool QuantDSplit::needsCheck( Theory::Effort e ) {
  return e >= Theory::EFFORT_FULL && !d_to_reduce.empty();
}

bool QuantDSplit::checkCompleteFor( Node q ) {
  // true if we split q
  return d_reduced.find(q) != d_reduced.end();
}

/* Call during quantifier engine's check */
void QuantDSplit::check(Theory::Effort e, QEffort quant_e)
{
  //add lemmas ASAP (they are a reduction)
  if (quant_e != QEFFORT_CONFLICT)
  {
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  FirstOrderModel* m = d_quantEngine->getModel();
  std::vector<Node> lemmas;
  for (const Node& q : d_to_reduce)
  {
    if (m->isQuantifierAsserted(q) && m->isQuantifierActive(q)
        && d_reduced.find(q) == d_reduced.end())
    {
      d_reduced.insert(q);
      std::vector<Node> disj;
      disj.push_back(q.negate());
      bool success = true;

      // have we expanded it?
      std::map<Node, Node>::iterator it = d_quant_to_expanded.find(q);
      if (it != d_quant_to_expanded.end())
      {
        disj.push_back(it->second);
      }
      else
      {
        std::map<Node, unsigned>::iterator it = d_quant_to_split.find(q);
        Assert(it != d_quant_to_split.end());
        std::vector<Node> bvs;
        for (unsigned i = 0; i < q[0].getNumChildren(); i++)
        {
          if (i != it->second)
          {
            bvs.push_back(q[0][i]);
          }
        }
        TNode svar = q[0][it->second];
        TypeNode tn = svar.getType();
        if (tn.isDatatype())
        {
          std::vector<Node> cons;
          const Datatype& dt = tn.getDatatype();
          for (unsigned j = 0, ncons = dt.getNumConstructors(); j < ncons; j++)
          {
            std::vector<Node> vars;
            for (unsigned k = 0, nargs = dt[j].getNumArgs(); k < nargs; k++)
            {
              TypeNode tns = TypeNode::fromType(dt[j][k].getRangeType());
              Node v = nm->mkBoundVar(tns);
              vars.push_back(v);
            }
            std::vector<Node> bvs_cmb;
            bvs_cmb.insert(bvs_cmb.end(), bvs.begin(), bvs.end());
            bvs_cmb.insert(bvs_cmb.end(), vars.begin(), vars.end());
            vars.insert(vars.begin(), Node::fromExpr(dt[j].getConstructor()));
            Node c = nm->mkNode(APPLY_CONSTRUCTOR, vars);
            TNode ct = c;
            Node body = q[1].substitute(svar, ct);
            if (!bvs_cmb.empty())
            {
              body =
                  nm->mkNode(FORALL, nm->mkNode(BOUND_VAR_LIST, bvs_cmb), body);
            }
            cons.push_back(body);
          }
          Node conc = cons.size() == 1 ? cons[0] : nm->mkNode(AND, cons);
          disj.push_back(conc);
        }
        else
        {
          Assert(false);
          success = false;
        }
      }
      if (success)
      {
        Node dlem = disj.size() == 1 ? disj[0] : nm->mkNode(OR, disj);
        Trace("quant-dsplit") << "QuantDSplit lemma : " << dlem << std::endl;
        d_quantEngine->addLemma(dlem, false);
      }
    }
  }
}

Node QuantDSplit::expand(Node q)
{
  NodeManager* nm = NodeManager::currentNM();
  // try to initialize the representative set for each type
  RepSet rs;
  for (unsigned i = 0, size = q[0].getNumChildren(); i < size; i++)
  {
    TypeNode tn = q[0][i].getType();
    uint32_t maxCard = std::numeric_limits<uint32_t>::max();
    if (!TermEnumeration::mayComplete(tn, maxCard))
    {
      Trace("quant-dsplit")
          << "...cannot expand type " << tn << "." << std::endl;
      return Node::null();
    }
    else
    {
      rs.complete(tn);
    }
  }
  std::vector<Node> conj;
  std::vector<Node> vars;
  for (const Node& v : q[0])
  {
    vars.push_back(v);
  }
  RepSetIterator riter(&rs);
  if (riter.setQuantifier(q))
  {
    std::vector<Node> subs;
    while (!riter.isFinished())
    {
      subs.clear();
      riter.getCurrentTerms(subs);
      Node inst =
          q[1].substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      conj.push_back(inst);
      riter.increment();
    }
  }
  else
  {
    Trace("quant-dsplit") << "...failed to initialize quantifier." << std::endl;
    return Node::null();
  }

  return nm->mkNode(AND, conj);
}
