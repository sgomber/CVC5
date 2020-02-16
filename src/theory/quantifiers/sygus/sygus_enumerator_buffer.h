/*********************                                                        */
/*! \file sygus_enumerator_buffer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_enumerator
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_ENUMERATOR_BUFFER_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_ENUMERATOR_BUFFER_H

#include <map>
#include <unordered_set>
#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include <vector>

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** SygusEnumeratorBuffer
 */
class SygusEnumeratorBuffer
{
 public:
  SygusEnumeratorBuffer(TermDbSygus* tds, ExampleEvalCache * eec);
  ~SygusEnumeratorBuffer() {}
  /** initialize this class with sygus enumerator e */
  void initialize(Node e);
  /** 
   * Add sygus constructor term n, called on terms that are unique up to
   * rewriting. Term bn is the builtin version of this term.
   */
  void addTerm(Node n, Node bn);
  /** 
   * Compute buffer, add the (sygus) terms to vector ts that are unique
   * up to example evaluation.
   */
  void computeBuffer(std::vector<Node>& ts);
private:
  /** pointer to term database sygus */
  TermDbSygus* d_tds;
  /** pointer to the synth conjecture that owns this enumerator */
  SynthConjecture* d_parent;
  /** 
   * maps sygus constructors to applications of that constructor that are in
   * the current buffer. 
   */
  std::map< Node, std::vector<Node> > d_buffer;
  /** TEMPORARY buffer */
  std::vector<Node> d_tbuffer;
  /** pointer to evaluation cache for enumerator */
  ExampleEvalCache* d_eec;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_ENUMERATOR_BUFFER_H */
