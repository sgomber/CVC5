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

SygusEnumeratorBuffer::SygusEnumeratorBuffer(TermDbSygus* tds, ExampleEvalCache * eec) : d_tds(tds), d_eec(eec)
{
  
}

void SygusEnumeratorBuffer::initialize(Node e)
{
  // ?
}

void SygusEnumeratorBuffer::addTerm(Node n, Node bn)
{
  //d_buffer[n.getOperator()].push_back(n);
  
  
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

void SygusEnumeratorBuffer::computeBuffer( std::vector<Node>& terms)
{
  
  
  /// NAIVE IMPLEMENTATION
  terms.insert(terms.end(),d_tbuffer.begin(),d_tbuffer.end());
  d_tbuffer.clear();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
