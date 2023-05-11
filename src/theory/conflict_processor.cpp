/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An assigner
 */

#include "theory/conflict_processor.h"

#include "expr/assigner.h"
#include "theory/theory_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

ConflictProcessor::ConflictProcessor(Env& env, TheoryEngine* te)
    : EnvObj(env), d_engine(te)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
}

TrustNode ConflictProcessor::processLemma(const TrustNode& lem)
{
  Node lemma = lem.getProven();
  Subs s;
  std::map<Node, Node> varToExp;
  std::vector<TNode> tgtLits;
  // decompose lemma into AND( s ) => OR( tgtLits )
  bool ok = decomposeLemma(lemma, s, varToExp, tgtLits);
  Trace("confp") << "Decomposed lemma " << lemma << std::endl;
  Trace("confp") << "- Substitution: " << s.toString() << std::endl;
  Trace("confp") << "- Target: " << tgtLits << std::endl;
  // if we encountered a simple conflict, return it
  if (!ok)
  {
    Trace("confp") << "Simple conflict for " << lemma << std::endl;
    // NOTE: trusting that it is minimzed here
    return lem;
  }
  // if we didn't infer a substitution, we are done
  if (s.empty())
  {
    return lem;
  }

  // check if the substitution implies one of the tgtLit, if not, we are done
  TNode tgtLit;
  for (TNode tlit : tgtLits)
  {
    if (checkSubstitution(s, tlit))
    {
      tgtLit = tlit;
      break;
    }
  }
  if (tgtLit.isNull())
  {
    return lem;
  }
  bool minimized = false;
  if (tgtLits.size()>1)
  {
    minimized = true;
    Trace("confp") << "Target suffices " << tgtLit << " for than one disjunct: " << lemma << std::endl;
  }

  // minimize the substitution

  // generalize the conflict
  bool generalized = false;
  for (std::pair<const Node, Node>& e : varToExp)
  {
    Node v = e.first;
    size_t vindex = s.getIndex(v);
    Assert(vindex < s.d_vars.size());
    // can we generalize to an assigner?
    std::vector<Assigner*> as = d_engine->getActiveAssigners(e.second);
    if (as.empty())
    {
      continue;
    }
    Node prev = s.d_subs[vindex];
    Node stgtLit = tgtLit;
    // if we have more than one substitution, apply the others
    if (s.size()>1)
    {
      s.d_subs[vindex] = v;
      stgtLit = s.apply(tgtLit);
    }
    Trace("confp") << "Check substitution literal " << e.second
                   << ", #assigners=" << as.size() << std::endl;
    for (Assigner* a : as)
    {
      if (checkGeneralizes(a, v, prev, stgtLit))
      {
        generalized = true;
        // update the explanation
        varToExp[v] = a->getSatLiteral();
        break;
      }
    }
    if (generalized)
    {
      break;
    }
  }
  // if we successfully generalized
  if (minimized || generalized)
  {
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> ant;
    for (std::pair<const Node, Node>& e : varToExp)
    {
      ant.push_back(e.second);
    }
    Node genLem = nm->mkNode(IMPLIES, nm->mkAnd(ant), tgtLit);
    return TrustNode::mkTrustLemma(genLem);
  }

  return lem;
}

bool ConflictProcessor::decomposeLemma(const Node& lem,
                                       Subs& s,
                                       std::map<Node, Node>& varToExp,
                                       std::vector<TNode>& tgtLits) const
{
  // visit is implicitly negated
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  std::unordered_set<Node> keep;
  TNode cur;
  Kind k;
  visit.push_back(lem);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      k = cur.getKind();
      if (k == OR || k == IMPLIES)
      {
        // all children are entailed
        for (size_t i = 0, nargs = cur.getNumChildren(); i < nargs; i++)
        {
          if (k == IMPLIES && i == 0)
          {
            Node cc = cur[0].negate();
            keep.insert(cc);
            visit.push_back(cc);
          }
          else
          {
            visit.push_back(cur[i]);
          }
        }
        continue;
      }
      else if (k == NOT)
      {
        k = cur[0].getKind();
        if (k == EQUAL)
        {
          // maybe substitution?
          Node vtmp;
          Node ctmp;
          if (Assigner::isAssignEq(cur[0], vtmp, ctmp))
          {
            Node cprev = s.getSubs(vtmp);
            if (!cprev.isNull() && ctmp != cprev)
            {
              Assert(varToExp.find(vtmp) != varToExp.end());
              return false;
            }
            s.add(vtmp, ctmp);
            varToExp[vtmp] = cur[0];
            continue;
          }
        }
        else if (k == AND)
        {
          for (const Node& c : cur[0])
          {
            Node cn = c.negate();
            keep.insert(cn);
            visit.push_back(cn);
          }
          continue;
        }
      }
      tgtLits.push_back(cur);
    }
  } while (!visit.empty());
  // no simple conflict
  return true;
}

bool ConflictProcessor::checkSubstitution(
    const Subs& s, const Node& tgtLit) const
{
  Node stgtLit = s.apply(tgtLit);
  stgtLit = rewrite(stgtLit);
  return stgtLit == d_true;
}

bool ConflictProcessor::checkGeneralizes(Assigner * a, const Node& v, const Node& s, const Node& tgtLit)
{
  std::tuple<Node, Node, Node> key(v, a->getSatLiteral(), tgtLit);
  std::map< std::tuple<Node, Node, Node>, bool>::iterator it = d_genCache.find(key);
  if (it!=d_genCache.end())
  {
    return it->second;
  }
  Subs subs;
  subs.add(v, s);
  const std::vector<Node>& assigns = a->getAssignments(v);
  std::unordered_set<Node> checked;
  checked.insert(s);
  for (const Node& ss : assigns)
  {
    if (checked.find(ss) != checked.end())
    {
      continue;
    }
    subs.d_subs[0] = ss;
    if (!checkSubstitution(subs, tgtLit))
    {
      Trace("confp") << "Failed for " << ss << std::endl;
      d_genCache[key] = false;
      return false;
    }
    checked.insert(ss);
  }
  d_genCache[key] = true;
  return true;
}

}  // namespace theory
}  // namespace cvc5::internal
