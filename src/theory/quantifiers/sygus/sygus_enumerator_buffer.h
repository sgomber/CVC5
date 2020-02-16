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
#include "expr/node.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/sygus/example_eval_cache.h"
#include "theory/quantifiers/sygus/sygus_stats.h"
#include "expr/node_trie.h"
#include <vector>

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * A trie that stores data at undetermined depth. Storing data at
 * undetermined depth is in contrast to the NodeTrie (expr/node_trie.h), which
 * assumes all data is stored at a fixed depth.
 *
 * Since data can be stored at any depth, we require both a d_children field
 * and a d_data field.
 */
class VariadicTrieEval
{
 public:
  /** the children of this node */
  std::map<Node, VariadicTrieEval> d_children;
  /** the data at this node */
  Node d_data;
  /**
   * Add data with identifier n indexed by i, return true if data is not already
   * stored at the node indexed by i.
   */
  bool add(Node n, const std::vector<Node>& i);
};

  
/** SygusEnumeratorBuffer
 */
class SygusEnumeratorBuffer
{
 public:
  SygusEnumeratorBuffer(TermDbSygus* tds, ExampleEvalCache * eec, SygusStatistics * s);
  ~SygusEnumeratorBuffer() {}
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
  /** TEMPORARY buffer */
  std::vector<Node> d_tbuffer;
  /** pointer to evaluation cache for enumerator */
  ExampleEvalCache* d_eec;
  /** reference to the statistics of parent */
  SygusStatistics* d_stats;
  /** node trie */
  std::map< Node, VariadicTrieEval > d_cache;
  std::map< Node, std::map< unsigned, VariadicTrieEval > > d_cacheEx;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_ENUMERATOR_BUFFER_H */
