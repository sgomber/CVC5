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
  ++d_stats.d_initLemmas;
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
  if (options().theory.conflictProcessMode
      == options::ConflictProcessMode::TEST)
  {
    return TrustNode::null();
  }
  // check if the substitution implies one of the tgtLit, if not, we are done
  Node tgtLit;
  for (TNode tlit : tgtLits)
  {
    if (checkSubstitution(s, tlit, nullptr))
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
  // NOTE: could minimize the substitution here?

  // the form of the target literal as it will appear in the final lemma.
  Node tgtLitFinal = tgtLit;
  // we are minimized if there were multiple target literals and we found a
  // single one that sufficed
  bool minimized = false;
  if (tgtLits.size() > 1)
  {
    minimized = true;
    ++d_stats.d_minLemmas;
    Trace("confp") << "Target suffices " << tgtLit
                   << " for more than one disjunct: " << lemma << std::endl;
  }

  // generalize the conflict
  bool generalized = false;
  bool isConflict = lem.getKind() == TrustNodeKind::CONFLICT;
  if (d_doGeneralize && d_env.hasAssigners())
  {
    // first, try to generalize the target literal
    Node tgtLitn = tgtLit.negate();
    Assigner* atgtGen = nullptr;
    std::vector<Assigner*> ast = d_engine->getActiveAssigners(tgtLitn);
    Trace("confp-debug") << "Check target literal " << tgtLitn
                         << ", #assigners=" << ast.size() << std::endl;
    for (Assigner* a : ast)
    {
      if (checkTgtGeneralizes(a, tgtLit, tgtLitFinal, s, isConflict))
      {
        ++d_stats.d_genLemmas;
        generalized = true;
        atgtGen = a;
        break;
      }
    }
    Trace("confp-debug") << "...target generalized=" << generalized
                         << std::endl;
    // second, try to generalize the substitution literals
    std::unordered_set<Assigner*> aprocessed;
    std::vector<Node> allVars;
    for (std::pair<const Node, Node>& e : varToExp)
    {
      allVars.push_back(e.first);
    }
    for (const Node& v : allVars)
    {
      Assert(varToExp.find(v) != varToExp.end());
      // can we generalize to an assigner?
      Node expv = varToExp[v];
      std::vector<Assigner*> as = d_engine->getActiveAssigners(expv);
      if (as.empty())
      {
        continue;
      }
      // NOTE: maybe don't generalize if multiple assigners?
      Trace("confp-debug") << "Check substitution literal " << expv
                           << ", #assigners=" << as.size() << std::endl;
      for (Assigner* a : as)
      {
        // if we haven't already processed this assigner
        if (aprocessed.find(a) != aprocessed.end())
        {
          continue;
        }
        aprocessed.insert(a);
        std::vector<Node> vs;
        Node stgtLit;
        if (s.size() == 1)
        {
          // if only one variable in substitution, we will try to generalize it
          vs.push_back(v);
          stgtLit = tgtLit;
        }
        else
        {
          const std::vector<Node>& alits = a->getLiterals();
          // otherwise, we partition into those that are in the assigner and
          // those that are not.
          Subs srem;
          for (const Node& vv : allVars)
          {
            // must check the explanation, not the variable itself
            if (v == vv
                || std::find(alits.begin(), alits.end(), varToExp[vv])
                       != alits.end())
            {
              vs.push_back(vv);
            }
            else
            {
              srem.add(vv, s.getSubs(vv));
            }
          }
          Assert(!vs.empty());
          // apply the substitution that is not included in this assigner
          stgtLit = srem.apply(tgtLit);
        }
        Trace("confp-debug2") << "Generalize variables are " << vs << std::endl;
        Trace("confp-debug2") << "Target literal is " << stgtLit << std::endl;
        Node genPred =
            checkSubsGeneralizes(a, vs, stgtLit, atgtGen, isConflict);
        if (!genPred.isNull())
        {
          if (!generalized)
          {
            generalized = true;
            ++d_stats.d_genLemmas;
          }
          // update the explanation
          varToExp[v] = genPred;
          for (size_t i = 1; i < vs.size(); i++)
          {
            varToExp.erase(vs[i]);
          }
          break;
        }
      }
      // NOTE: can't generalize across multiple assigners
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
                // replace the previous if we have an assigner
                tgtLits.push_back(prevExp.notNode());
                s.erase(vtmp);
              }
              else
              {
                // otherwise, just take this as a target literal
                tgtLits.push_back(cur);
                continue;
              }
            }
            // use as a substitution
            s.add(vtmp, ctmp);
            varToExp[vtmp] = cur[0];
            continue;
          }
        }
        else if (k == AND)
        {
          // negations of children of AND are entailed
          for (const Node& c : cur[0])
          {
            Node cn = c.negate();
            keep.insert(cn);
            visit.push_back(cn);
          }
          continue;
        }
      }
      // otherwise, take this as a target literal
      tgtLits.push_back(cur);
    }
  } while (!visit.empty());
}

bool ConflictProcessor::hasAssigner(const Node& lit) const
{
  return !d_env.getAssignersFor(lit).empty();
}

bool ConflictProcessor::checkSubstitution(const Subs& s,
                                          const Node& tgtLit,
                                          Assigner* atgt) const
{
  bool expect = true;
  Node tgtAtom = tgtLit;
  if (tgtAtom.getKind() == NOT)
  {
    tgtAtom = tgtAtom[0];
    expect = false;
  }
  // optimize for OR, since we may have generalized a target
  Kind k = tgtAtom.getKind();
  if (k == OR)
  {
    for (const Node& n : tgtAtom)
    {
      Node sn = evaluate(n, s.d_vars, s.d_subs);
      if (!sn.isConst())
      {
        // failure if all disjuncts must be false
        if (!expect)
        {
          return false;
        }
      }
      else if (sn.getConst<bool>())
      {
        // success if short circuits to true
        return expect;
      }
    }
    return true;
  }
  // otherwise, rewrite
  Node stgtAtom = evaluate(tgtAtom, s.d_vars, s.d_subs);
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
    if (!checkSubstitution(s, ln, nullptr))
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
                                             const std::vector<Node>& vs,
                                             const Node& tgtLit,
                                             Assigner* atgt,
                                             bool& isConflict)
{
  Assert(!vs.empty());
  std::pair<Node, Node> key(a->getSatLiteral(), tgtLit);
  std::map<std::pair<Node, Node>, Node>::iterator it = d_genCache.find(key);
  if (it != d_genCache.end())
  {
    return it->second;
  }
  size_t nvars = vs.size();
  Subs subs;
  for (const Node& v : vs)
  {
    subs.add(v, v);
  }
  std::vector<size_t> vindices;
  if (nvars>1)
  {
    for (const Node& v : vs)
    {
      vindices.push_back(a->variableIndexOf(v));
    }
  }
  std::vector<size_t> fails;
  options::ConflictProcessMode mode = options().theory.conflictProcessMode;
  size_t nassigns = a->getNode().getNumChildren();
  bool successAssign = false;
  const std::map<Node, std::vector<size_t>>& amap =
      a->getAssignmentMap();
  for (const std::pair<const Node, std::vector<size_t>>& aa : amap)
  {
    Trace("ajr-temp") << "#" << aa.first << " = " << aa.second.size()
                      << std::endl;
    successAssign = false;
    if (nvars==1)
    {
      Assert (aa.first.getType()==vs[0].getType());
      subs.d_subs[0] = aa.first;
    }
    else
    {
      Assert (aa.first.getKind()==SEXPR);
      for (size_t j=0; j<nvars; j++)
      {
        Assert (j<vindices.size());
        subs.d_subs[j] = aa.first[vindices[j]];
      }
    }
    successAssign = checkSubstitution(subs, tgtLit, atgt);
    if (!successAssign)
    {
      fails.insert(fails.end(), aa.second.begin(), aa.second.end());
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
    : d_initLemmas(sr.registerInt("ConflictProcessor::init_lemmas")),
      d_lemmas(sr.registerInt("ConflictProcessor::lemmas")),
      d_minLemmas(sr.registerInt("ConflictProcessor::min_lemmas")),
      d_genLemmas(sr.registerInt("ConflictProcessor::gen_lemmas"))
{
}

}  // namespace theory
}  // namespace cvc5::internal
