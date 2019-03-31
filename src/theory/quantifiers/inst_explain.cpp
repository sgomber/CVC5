/*********************                                                        */
/*! \file inst_explain.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of instantiate
 **/

#include "theory/quantifiers/inst_explain.h"

#include "options/quantifiers_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void InstExplainLit::initialize(Node inst)
{
  d_this = inst;
}
void InstExplainLit::reset()
{
  d_curr_prop_insts.clear();
}
void InstExplainLit::addInstExplanation(Node inst)
{
  if (std::find(d_insts.begin(), d_insts.end(), inst) == d_insts.end())
  {
    d_insts.push_back(inst);    
  }
}

void InstExplainLit::setPropagating(Node inst)
{
  Assert( std::find(d_curr_prop_insts.begin(),d_curr_prop_insts.end(),inst)==d_curr_prop_insts.end() );
  Assert( std::find(d_inst.begin(),d_inst.end(),inst)!=d_inst.end());
  d_curr_prop_insts.push_back(inst);
  // TODO: get the explanation?
}

void InstExplainInst::initialize(Node inst)
{
  d_this = inst;
}

void InstExplainInst::propagate( QuantifiersEngine * qe, std::vector< Node >& propLits )
{
  // if possible, propagate the literal in the clause that must be true
  
  
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
