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
#include "options/theory_options.h"
#include "theory/theory_engine.h"
#include "expr/skolem_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

ConflictProcessor::ConflictProcessor(Env& env, TheoryEngine* te)
    : EnvObj(env), d_engine(te)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  options::ConflictProcessMode mode = options().theory.conflictProcessMode;
  Assert(mode != options::ConflictProcessMode::NONE);
  d_generalizeMaj = (mode == options::ConflictProcessMode::GENERALIZE_MAJORITY);
  d_generalizeAny = (mode == options::ConflictProcessMode::GENERALIZE_ANY);
  d_doGeneralize = (mode == options::ConflictProcessMode::GENERALIZE_ALL
                    || d_generalizeMaj || d_generalizeAny);
}

TrustNode ConflictProcessor::processLemma(const TrustNode& lem)
{
  Node lemma = lem.getProven();
  Subs s;
  std::map<Node, Node> varToExp;
  std::vector<TNode> tgtLits;
  // decompose lemma into AND( s ) => OR( tgtLits )
  decomposeLemma(lemma, s, varToExp, tgtLits);
  Trace("confp") << "Decomposed " << lemma << std::endl;
  Trace("confp") << "- Substitution: " << s.toString() << std::endl;
  Trace("confp") << "- Target: " << tgtLits << std::endl;
  // if we didn't infer a substitution, we are done
  if (s.empty())
  {
    return TrustNode::null();
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
    return TrustNode::null();
  }
  // we are minimized if there were multiple target literals and we found a
  // single one that sufficed
  bool minimized = false;
  if (tgtLits.size() > 1)
  {
    minimized = true;
    Trace("confp") << "Target suffices " << tgtLit
                   << " for than one disjunct: " << lemma << std::endl;
  }

  // generalize the conflict
  bool generalized = false;
  bool isConflict = lem.getKind() == TrustNodeKind::CONFLICT;
  if (d_doGeneralize && d_env.hasAssigners())
  {
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
      // TODO: parallel substitution
      if (s.size() > 1)
      {
        s.d_subs[vindex] = v;
        stgtLit = s.apply(tgtLit);
      }
      Trace("confp") << "Check substitution literal " << e.second
                     << ", #assigners=" << as.size() << std::endl;
      for (Assigner* a : as)
      {
        Node alit = checkGeneralizes(a, v, prev, stgtLit, isConflict);
        if (!alit.isNull())
        {
          generalized = true;
          // update the explanation
          varToExp[v] = alit;
          break;
        }
      }
      if (generalized)
      {
        break;
      }
    }
  }
  Trace("confp") << "...minimized=" << minimized
                 << ", generalized=" << generalized << std::endl;
  // if we successfully generalized
  if (minimized || generalized)
  {
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> clause;
    for (std::pair<const Node, Node>& e : varToExp)
    {
      if (e.second.getKind() == AND)
      {
        for (const Node& ec : e.second)
        {
          clause.push_back(ec.negate());
        }
      }
      else
      {
        clause.push_back(e.second.negate());
      }
    }
    clause.push_back(tgtLit);
    Node genLem = nm->mkOr(clause);
    // AlwaysAssert(false) << genLem << " for " << lem << std::endl;
    return TrustNode::mkTrustLemma(genLem);
  }
  return TrustNode::null();
}

void ConflictProcessor::decomposeLemma(const Node& lem,
                                       Subs& s,
                                       std::map<Node, Node>& varToExp,
                                       std::vector<TNode>& tgtLits) const
{
  std::map<Node, bool> hasAssigners;
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
            if (!cprev.isNull())
            {
              if (ctmp == cprev)
              {
                // redundant (duplicate equality)
                continue;
              }
              Assert(varToExp.find(vtmp) != varToExp.end());
              Node prevExp = varToExp[vtmp];
              if (!hasAssigner(prevExp) && hasAssigner(cur[0]))
              {
                // replace the previous
                tgtLits.push_back(prevExp.notNode());
                s.erase(vtmp);
              }
              else
              {
                // take this as a target literal
                tgtLits.push_back(cur);
                continue;
              }
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
}

bool ConflictProcessor::hasAssigner(const Node& lit) const
{
  return !d_env.getAssignersFor(lit).empty();
}

bool ConflictProcessor::checkSubstitution(const Subs& s,
                                          const Node& tgtLit) const
{
  Node stgtLit = s.apply(tgtLit);
  stgtLit = rewrite(stgtLit);
  return stgtLit == d_true;
}

Node ConflictProcessor::checkGeneralizes(Assigner* a,
                                         const Node& v,
                                         const Node& s,
                                         const Node& tgtLit,
                                         bool& isConflict)
{
  std::tuple<Node, Node, Node> key(v, a->getSatLiteral(), tgtLit);
  std::map<std::tuple<Node, Node, Node>, Node>::iterator it =
      d_genCache.find(key);
  if (it != d_genCache.end())
  {
    return it->second;
  }
  Subs subs;
  subs.add(v, s);
  const std::vector<Node>& assigns = a->getAssignments(v);
  Assert (a->getNode().getNumChildren()==assigns.size());
  std::unordered_set<Node> checked;
  checked.insert(s);
  std::vector<size_t> fails;
  for (size_t i=0, nassigns = assigns.size(); i<nassigns; i++)
  {
    Node ss = assigns[i];
    if (checked.find(ss) != checked.end())
    {
      continue;
    }
    subs.d_subs[0] = ss;
    if (!checkSubstitution(subs, tgtLit))
    {
      Trace("confp") << "Failed for " << ss << std::endl;
      fails.push_back(i);
      if (!d_generalizeMaj)
      {
        break;
      }
    }
    checked.insert(ss);
  }
  Node ret;
  // generalize
  if (fails.empty() || (d_generalizeMaj && 2 * fails.size() < checked.size())
      || (d_generalizeAny && fails.size() + 1 < checked.size()))
  {
    isConflict = isConflict && fails.empty();
    Trace("confp") << "...generalize with " << fails.size() << " / "
                   << checked.size() << " literals from assigner" << std::endl;
    ret = a->getSatLiteral();
    if (!fails.empty())
    {
      NodeManager* nm = NodeManager::currentNM();
      SkolemManager * skm = nm->getSkolemManager();
      std::vector<Node> conj;
      conj.push_back(ret);
      const Node& anode = a->getNode();
      for (size_t i : fails)
      {
        Assert (i<anode.getNumChildren());
        Node adisj = anode[i];
        if (options().theory.assignerProxy)
        {
          adisj = skm->mkProxyLit(adisj);
        }
        conj.push_back(adisj.notNode());
      }
      ret = nm->mkAnd(conj);
    }
  }
  d_genCache[key] = ret;
  return ret;
}

}  // namespace theory
}  // namespace cvc5::internal
