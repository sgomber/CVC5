/*********************                                                        */
/*! \file sygus_enumerator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_enumerator
 **/

#include "theory/quantifiers/sygus/sygus_enumerator_buffer.h"

#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/sygus/synth_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
bool VariadicTrieEval::add(Node n, const std::vector<Node>& i)
{
  VariadicTrieEval* curr = this;
  for (const Node& ic : i)
  {
    curr = &(curr->d_children[ic]);
  }
  if (curr->d_data.isNull())
  {
    curr->d_data = n;
    return true;
  }
  return false;
}

SygusEnumeratorBuffer::SygusEnumeratorBuffer(TermDbSygus* tds, ExampleEvalCache * eec, SygusStatistics * s) : d_tds(tds), d_eec(eec), d_stats(s)
{
  
}

void SygusEnumeratorBuffer::addTerm(Node n, Node bn)
{
  /// NAIVE IMPLEMENTATION
  // Is it equivalent under examples?
  Node bne = d_eec->addSearchVal(bn);
  if (!bne.isNull())
  {
    if (bn != bne)
    {
      Trace("sygus-enum-exc")
          << "Exclude (by examples): " << bn << ", since we already have "
          << bne << std::endl;
      return;
    }
  }
  d_tbuffer.push_back(n);
}

void SygusEnumeratorBuffer::notifyTerm(Node n, Node bn)
{
  std::vector< std::vector< Node > > childrenEval;
  for (const Node& nc : n)
  {
    Node bnc = datatypes::utils::sygusToBuiltin(nc);
    std::vector< Node > eval;
    d_eec->evaluateVec(bnc,eval);
    childrenEval.push_back(eval);
  }
  if( !childrenEval.empty())
  {
    AlwaysAssert(!childrenEval[0].empty());
    VariadicTrieEval * vte = &d_cache[n.getOperator()];
    unsigned nchildren = childrenEval.size();
    for (unsigned i=0, csize=childrenEval[0].size(); i<csize; i++)
    {
      //VariadicTrieEval * vte = &d_cacheEx[n.getOperator()][i];
      std::vector<Node> index;
      for (unsigned j=0; j<nchildren; j++)
      {
        index.push_back(childrenEval[j][i]);
      }
      if (vte->add(n,index))
      {
        ++(d_stats->d_evalMiss);
      }
      else
      {
        ++(d_stats->d_evalHit);
      }
    }
  }
}

void SygusEnumeratorBuffer::computeBuffer( std::vector<Node>& terms)
{
  
  
  /// NAIVE IMPLEMENTATION
  terms.insert(terms.end(),d_tbuffer.begin(),d_tbuffer.end());
  d_tbuffer.clear();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
