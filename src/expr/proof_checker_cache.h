/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof checker cache utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__PROOF_CHECKER_CACHE_H
#define CVC5__EXPR__PROOF_CHECKER_CACHE_H

#include <map>

#include "expr/node.h"
#include "expr/proof_rule.h"
#include "util/statistics_stats.h"

namespace cvc5 {

class ProofCheckerCacheTrie
{
public:
  /** The children of the trie */
  std::map<Node, ProofCheckerCacheTrie> d_children;
  /** The result of what the current rule checks */
  Node d_res;
};

/** A class for checking proofs */
class ProofCheckerCache
{
 public:
  ProofCheckerCache(){}
  ~ProofCheckerCache() {}
  /** Lookup */
  Node lookup(PfRule id,
                     const std::vector<Node>& cchildren,
                     const std::vector<Node>& args) const;
  /** Store */
  void store(PfRule id,
                     const std::vector<Node>& cchildren,
                     const std::vector<Node>& args,
                     Node res
            );
 private:
   /** The cache of proof checking */
  std::map< PfRule,  ProofCheckerCacheTrie > d_data;
};

}  // namespace cvc5

#endif /* CVC5__EXPR__PROOF_CHECKER_H */
