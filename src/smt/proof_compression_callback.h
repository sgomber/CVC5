/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for final processing proof nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PROOF_COMPRESSION_CALLBACK_H
#define CVC5__SMT__PROOF_COMPRESSION_CALLBACK_H

#include <map>
#include <sstream>
#include <unordered_set>

#include "proof/proof_node_updater.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace smt {

/** Compression callback class, for stats and pedantic checking */
class ProofCompressionCallback : protected EnvObj,
                                 public ProofNodeUpdaterCallback
{
 public:
  ProofCompressionCallback(Env& env);
  /**
   * Initialize, called once for each new ProofNode to process. This initializes
   * static information to be used by successive calls to update.
   */
  void analyze(std::shared_ptr<ProofNode> pn);
  /** Should proof pn be updated? */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /** Update the proof rule application. */
  bool update(Node res,
              PfRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;
  /** Get unprocessed scopes */
  std::unordered_set<std::shared_ptr<ProofNode>>& getUnprocessedScopes();

 private:
  std::unordered_map<Node, std::shared_ptr<ProofNode>> d_proven;
  /** List of scopes */
  std::unordered_set<std::shared_ptr<ProofNode>> d_unprocessedScopes;
};

class ProofCompressor : protected EnvObj
{
 public:
  /**
   * @param env The environment we are using
   */
  ProofCompressor(Env& env);
  /** compress */
  void compress(std::shared_ptr<ProofNode> pn);

 private:
  /** The compressor callback */
  ProofCompressionCallback d_ccb;
  /**
   * The updater, which is responsible for expanding macros in the final proof
   * and connecting preprocessed assumptions to input assumptions.
   */
  ProofNodeUpdater d_compressor;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
