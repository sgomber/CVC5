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
#include "expr/skolem_manager.h"
#include "options/theory_options.h"
#include "theory/theory_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

bool isFailure(options::ConflictProcessMode mode, size_t ntests, size_t nfails)
{
  switch (mode)
  {
    case options::ConflictProcessMode::GENERALIZE_ALL: return nfails > 0;
    case options::ConflictProcessMode::GENERALIZE_MAJORITY:
      return 2 * nfails >= ntests;
    case options::ConflictProcessMode::GENERALIZE_ALL_MINUS_ONE:
      return nfails > 1;
    case options::ConflictProcessMode::GENERALIZE_ANY:
      return nfails + 2 >= ntests;
    default: break;
  }
  return false;
}

ConflictProcessor::ConflictProcessor(Env& env, TheoryEngine* te)
    : EnvObj(env), d_engine(te), d_stats(statisticsRegistry())
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  options::ConflictProcessMode mode = options().theory.conflictProcessMode;
  Assert(mode != options::ConflictProcessMode::NONE);
  d_doGeneralize = (mode != options::ConflictProcessMode::MINIMIZE);
}

TrustNode ConflictProcessor::processLemma(const TrustNode& lem)
{
  Node lemma = lem.getProven();
  lemma = rewrite(lemma);
  Subs s;
  std::map<Node, Node> varToExp;
  std::vector<TNode> tgtLits;
  // decompose lemma into AND( s ) => OR( tgtLits )
  decomposeLemma(lemma, s, varToExp, tgtLits);
  // if we didn't infer a substitution, we are done
  if (s.empty())
  {
    Trace("confp-debug") << "...no substitution for " << lemma << std::endl;
    return TrustNode::null();
  }
  ++d_stats.d_lemmas;
  Trace("confp") << "Decomposed " << lemma << std::endl;
  Trace("confp") << "- Substitution: " << s.toString() << std::endl;
  Trace("confp") << "- Target: " << tgtLits << std::endl;
  // check if the substitution implies one of the tgtLit, if not, we are done
  Node tgtLit;
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
    Trace("confp-debug") << "No target for " << lemma << std::endl;
    return TrustNode::null();
  }
  Node tgtLitFinal = tgtLit;
  // we are minimized if there were multiple target literals and we found a
  // single one that sufficed
  bool minimized = false;
  if (tgtLits.size() > 1)
  {
    minimized = true;
    ++d_stats.d_minLemmas;
    Trace("confp") << "Target suffices " << tgtLit
                   << " for than one disjunct: " << lemma << std::endl;
  }

  // generalize the conflict
  bool generalized = false;
  bool isConflict = lem.getKind() == TrustNodeKind::CONFLICT;
  if (d_doGeneralize && d_env.hasAssigners())
  {
    // generalize the target literal
    Node tgtLitn = tgtLit.negate();
    std::vector<Assigner*> ast = d_engine->getActiveAssigners(tgtLitn);
    Trace("confp-debug") << "Check target literal " << tgtLitn
                         << ", #assigners=" << ast.size() << std::endl;
    for (Assigner* a : ast)
    {
      if (checkTgtGeneralizes(a, tgtLit, tgtLitFinal, s, isConflict))
      {
        generalized = true;
        break;
      }
    }
    Trace("confp-debug") << "...target generalized=" << generalized
                         << std::endl;
    // generalize the substitution literals
    for (std::pair<const Node, Node>& e : varToExp)
    {
      // can we generalize to an assigner?
      std::vector<Assigner*> as = d_engine->getActiveAssigners(e.second);
      if (as.empty())
      {
        continue;
      }
      Node v = e.first;
      size_t vindex = s.getIndex(v);
      Assert(vindex < s.d_vars.size());
      Node prev = s.d_subs[vindex];
      Node stgtLit = tgtLit;
      // if we have more than one substitution, apply the others
      // TODO: parallel substitution
      if (s.size() > 1)
      {
        s.d_subs[vindex] = v;
        stgtLit = s.apply(tgtLit);
      }
      Trace("confp-debug") << "Check substitution literal " << e.second
                           << ", #assigners=" << as.size() << std::endl;
      Trace("confp-debug2") << "Target literal is " << stgtLit << std::endl;
      for (Assigner* a : as)
      {
        Node genPred = checkSubsGeneralizes(a, v, prev, stgtLit, isConflict);
        if (!genPred.isNull())
        {
          generalized = true;
          ++d_stats.d_genLemmas;
          // update the explanation
          varToExp[v] = genPred;
          break;
        }
      }
      if (generalized)
      {
        break;
      }
      s.d_subs[vindex] = prev;
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
    if (tgtLitFinal.getKind() == OR)
    {
      clause.insert(clause.end(), tgtLitFinal.begin(), tgtLitFinal.end());
    }
    else
    {
      clause.push_back(tgtLitFinal);
    }
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
  bool expect = true;
  Node tgtAtom = tgtLit;
  if (tgtAtom.getKind() == NOT)
  {
    tgtAtom = tgtAtom[0];
    expect = false;
  }
  // optimize for (negated) OR, since we may have generalized a target
  Kind k = tgtAtom.getKind();
  if (k == OR)
  {
    for (const Node& n : tgtAtom)
    {
      Node sn = s.apply(n);
      sn = rewrite(sn);
      if (!sn.isConst())
      {
        if (!expect)
        {
          return false;
        }
      }
      else if (sn.getConst<bool>())
      {
        return expect;
      }
    }
    return true;
  }
  Node stgtAtom = s.apply(tgtAtom);
  stgtAtom = rewrite(stgtAtom);
  return stgtAtom.isConst() && stgtAtom.getConst<bool>() == expect;
}

bool ConflictProcessor::checkTgtGeneralizes(Assigner* a,
                                            Node& tgtLit,
                                            Node& tgtLitFinal,
                                            const Subs& s,
                                            bool& isConflict)
{
  Node anode = a->getNode();
  Assert(anode.getKind() == OR);
  Trace("confp-debug") << "...check target generalization " << anode
                       << std::endl;
  // check implies *all* literals
  options::ConflictProcessMode mode = options().theory.conflictProcessMode;
  size_t nargs = anode.getNumChildren();
  std::vector<Node> fails;
  std::vector<Node> success;
  for (size_t i = 0; i < nargs; i++)
  {
    Node ln = anode[i].negate();
    if (!checkSubstitution(s, ln))
    {
      fails.push_back(anode[i]);
      Trace("confp-debug") << "...failed for " << ln << std::endl;
      // see if we are a failure based on the mode
      if (isFailure(mode, nargs, i + 1 - success.size()))
      {
        return false;
      }
    }
    else
    {
      success.push_back(anode[i]);
    }
  }
  Trace("confp-debug") << "...target success!" << std::endl;
  if (success.size() < nargs)
  {
    NodeManager* nm = NodeManager::currentNM();
    isConflict = false;
    tgtLit = nm->mkOr(success).negate();
    fails.push_back(a->getSatLiteral().negate());
    tgtLitFinal = nm->mkOr(fails);
  }
  else
  {
    tgtLit = anode.negate();
    tgtLitFinal = a->getSatLiteral().negate();
  }
  return true;
}

Node ConflictProcessor::checkSubsGeneralizes(Assigner* a,
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
  Assert(a->getNode().getNumChildren() == assigns.size());
  std::vector<size_t> fails;
  bool successAssign = false;
  options::ConflictProcessMode mode = options().theory.conflictProcessMode;
  size_t nassigns = assigns.size();
  // note that we may have many duplicate assignments for v e.g. if
  // (or (and (= v c1) F1) ... (and (= v c1) F{n-1}) (and (= v c2) Fn))
  std::map<Node, bool> checked;
  std::map<Node, bool>::iterator itc;
  for (size_t i = 0; i < nassigns; i++)
  {
    Node ss = assigns[i];
    itc = checked.find(ss);
    if (itc == checked.end())
    {
      successAssign = false;
      if (!ss.isNull())
      {
        subs.d_subs[0] = ss;
        successAssign = checkSubstitution(subs, tgtLit);
      }
      checked[ss] = successAssign;
    }
    else
    {
      successAssign = itc->second;
    }
    if (!successAssign)
    {
      Trace("confp-debug") << "Failed for " << ss << std::endl;
      fails.push_back(i);
      // see if we are a failure based on the mode
      if (isFailure(mode, nassigns, fails.size()))
      {
        d_genCache[key] = Node::null();
        return Node::null();
      }
    }
  }
  isConflict = isConflict && fails.empty();
  Trace("confp") << "...generalize with " << fails.size() << " / " << nassigns
                 << " failed literals from assigner" << std::endl;
  Node ret = a->getSatLiteral();
  if (!fails.empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* skm = nm->getSkolemManager();
    std::vector<Node> conj;
    conj.push_back(ret);
    const Node& anode = a->getNode();
    for (size_t i : fails)
    {
      Assert(i < anode.getNumChildren());
      Node adisj = anode[i];
      if (options().theory.assignerProxy)
      {
        adisj = skm->mkProxyLit(adisj);
      }
      conj.push_back(adisj.notNode());
    }
    ret = nm->mkAnd(conj);
  }
  d_genCache[key] = ret;
  return ret;
}

ConflictProcessor::Statistics::Statistics(StatisticsRegistry& sr)
    : d_lemmas(sr.registerInt("ConflictProcessor::lemmas")),
      d_minLemmas(sr.registerInt("ConflictProcessor::min_lemmas")),
      d_genLemmas(sr.registerInt("ConflictProcessor::gen_lemmas"))
{
}

}  // namespace theory
}  // namespace cvc5::internal
