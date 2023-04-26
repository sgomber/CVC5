/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of module for final processing proof nodes.
 */

#include "smt/proof_compression_callback.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

ProofCompressionCallback::ProofCompressionCallback(Env& env) : EnvObj(env) {}

void ProofCompressionCallback::analyze(std::shared_ptr<ProofNode> pn)
{
  d_proven.clear();
  std::unordered_set<std::shared_ptr<ProofNode>> visited;
  std::unordered_set<std::shared_ptr<ProofNode>>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  visit.push_back(pn);
  std::shared_ptr<ProofNode> cur;
  while (!visit.empty())
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited.insert(cur);
      d_proven[cur->getResult()] = cur;
      if (cur->getRule() != PfRule::SCOPE)
      {
        const std::vector<std::shared_ptr<ProofNode>>& children =
            cur->getChildren();
        for (const std::shared_ptr<ProofNode>& cp : children)
        {
          visit.push_back(cp);
        }
      }
      else
      {
        d_unprocessedScopes.insert(cur);
      }
    }
  }
}

bool ProofCompressionCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                            const std::vector<Node>& fa,
                                            bool& continueUpdate)
{
  return false;
}
bool ProofCompressionCallback::update(Node res,
                                      PfRule id,
                                      const std::vector<Node>& children,
                                      const std::vector<Node>& args,
                                      CDProof* cdp,
                                      bool& continueUpdate)
{
  return false;
}

std::unordered_set<std::shared_ptr<ProofNode>>&
ProofCompressionCallback::getUnprocessedScopes()
{
  return d_unprocessedScopes;
}

ProofCompressor::ProofCompressor(Env& env)
    : EnvObj(env), d_ccb(env), d_compressor(env, d_ccb)
{
}
void ProofCompressor::compress(std::shared_ptr<ProofNode> pn)
{
  std::unordered_set<std::shared_ptr<ProofNode>> visited;
  std::unordered_set<std::shared_ptr<ProofNode>>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  visit.push_back(pn);
  std::shared_ptr<ProofNode> cur;
  while (!visit.empty())
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited.insert(cur);
      d_ccb.analyze(cur);
      d_compressor.process(pn);
      // FIXME: could be that a SCOPE is no longer used in compressed proof
      std::unordered_set<std::shared_ptr<ProofNode>>& scopes =
          d_ccb.getUnprocessedScopes();
      visit.insert(visit.end(), scopes.begin(), scopes.end());
    }
  }
}

}  // namespace smt
}  // namespace cvc5::internal
