/*********************                                                        */
/*! \file combination_model_based.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a care graph based approach for theory combination.
 **/

#include "theory/combination_model_based.h"

#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

CombinationModelBased::CombinationModelBased(
    TheoryEngine& te, const std::vector<Theory*>& paraTheories)
    : CombinationEngine(te, paraTheories)
{
}

CombinationModelBased::~CombinationModelBased() {}

bool CombinationModelBased::buildModel()
{
  // model was already built in combine theories
  Assert(d_mmanager->isModelBuilt());
  return d_mmanager->buildModel();
}

void CombinationModelBased::combineTheories()
{
  // push a SAT context
  context::Context* c = d_te.getSatContext();
  c->push();
  
  // TODO: change the notification class of the model's equality engine?
  eq::EqualityEngine * mee = d_eemanager->getModelEqualityEngine();
  
  
  // TODO

  // TODO: change the notification class of the ee back if central?
  
  
  
  c->pop();
}

void CombinationModelBased::eqNotifyNewClass(TNode t)
{
  // if it is a shared term, track the equivalence class
  if (d_sharedTerms->isShared(t))
  {
    if (d_shared_terms_merge.find(t) == d_shared_terms_merge.end())
    {
      d_shared_terms_merge[t].push_back(t);
    }
    else
    {
      // FIXME
    }
  }
}

void CombinationModelBased::eqNotifyMerge(TNode t1, TNode t2)
{
  mergeSharedTermEqcs(t1, t2);
}

void CombinationModelBased::mergeSharedTermEqcs(TNode t1, TNode t2)
{
  // equivalence classes on the model have merged, update the shared term
  // equivalence classes
  std::map<TNode, std::vector<TNode>>::iterator it2 =
      d_shared_terms_merge.find(t2);
  if (it2 != d_shared_terms_merge.end())
  {
    std::map<TNode, std::vector<TNode>>::iterator it1 =
        d_shared_terms_merge.find(t1);
    if (it1 != d_shared_terms_merge.end())
    {
      std::vector<TNode> merge;
      for (const TNode& b : it2->second)
      {
        // only care if not propagated equal to an existing one
        bool success = true;
        for (const TNode& a : it1->second)
        {
          if (d_sharedTerms->areEqual(a, b))
          {
            success = false;
            break;
          }
        }
        if (success)
        {
          merge.push_back(b);
        }
      }
      it1->second.insert(it1->second.end(), merge.begin(), merge.end());
    }
    else
    {
      d_shared_terms_merge[t1] = d_shared_terms_merge[t2];
    }
    d_shared_terms_merge.erase(it2);
  }
}

unsigned CombinationModelBased::checkPair(TNode a,
                                          TNode b,
                                          TheoryId tid,
                                          bool tparametric)
{
  Trace("tc-model-debug-pair")
      << "Check pair " << a << " <> " << b << " with " << tid << std::endl;
  if (d_sharedTerms->isShared(a) && d_sharedTerms->isShared(b)
      && !d_sharedTerms->areDisequal(a, b))
  {
    EqualityStatus es = d_te.theoryOf(tid)->getEqualityStatus(a, b);
    Assert(es != EQUALITY_TRUE_AND_PROPAGATED);
    Assert(es != EQUALITY_FALSE_AND_PROPAGATED);
    Trace("tc-model-debug")
        << "    " << a << " and " << b << " have equality status " << es
        << " in " << tid << std::endl;
    if (es == EQUALITY_TRUE || es == EQUALITY_TRUE_IN_MODEL)
    {
      // Case that a == b
      if (d_sharedEq[a].find(b) == d_sharedEq[a].end() || tparametric)
      {
        d_sharedEq[a][b] = tid;
      }
    }
    else if (es == EQUALITY_FALSE || es == EQUALITY_FALSE_IN_MODEL)
    {
      // Case that a != b
      if (d_sharedDeq[a].find(b) == d_sharedDeq[a].end() || tparametric)
      {
        d_sharedDeq[a][b] = tid;
      }
    }
    else if (es == EQUALITY_UNKNOWN)
    {
      // Case that a =? b
      if (d_sharedEq[a].find(b) == d_sharedEq[a].end())
      {
        d_sharedEq[a][b] = tid;
      }
      if (d_sharedDeq[a].find(b) == d_sharedDeq[a].end())
      {
        d_sharedDeq[a][b] = tid;
      }
    }
  }
  // TODO : do the check split candidate here
  return 0;
}

unsigned CombinationModelBased::checkSharedTermMaps(
    const std::map<TheoryId, std::unordered_set<TNode, TNodeHashFunction>>&
        tshared)
{
  unsigned numSplits = 0;

  for (const std::pair<const TNode,
                       std::unordered_map<TNode, TheoryId, TNodeHashFunction>>&
           eq : d_sharedEq)
  {
    TNode a = eq.first;
    std::unordered_map<TNode,
                       std::unordered_map<TNode, TheoryId, TNodeHashFunction>,
                       TNodeHashFunction>::const_iterator deq =
        d_sharedDeq.find(a);
    if (deq != d_sharedDeq.end())
    {
      for (const std::pair<const TNode, TheoryId>& eq_lhs : eq.second)
      {
        TNode b = eq_lhs.first;
        std::unordered_map<TNode, TheoryId, TNodeHashFunction>::const_iterator
            deq_lhs = deq->second.find(b);
        if (deq_lhs != deq->second.end())
        {
          TheoryId tid_eq = eq_lhs.second;
          TheoryId tid_deq = deq_lhs->second;
          Trace("tc-model-debug")
              << "Split candidate : " << a << " <> " << b << std::endl;
          Trace("tc-model-debug")
              << "   true/unknown in : " << tid_eq
              << " (parametric : " << isParametric(tid_eq) << ")" << std::endl;
          Trace("tc-model-debug")
              << "  false/unknown in : " << tid_deq
              << " (parametric : " << isParametric(tid_deq) << ")" << std::endl;
          numSplits += checkSplitCandidate(a, b, tid_eq, tid_deq);
        }
      }
    }
  }
  return numSplits;
}

unsigned CombinationModelBased::checkSplitCandidate(TNode a,
                                                    TNode b,
                                                    theory::TheoryId t1,
                                                    theory::TheoryId t2)
{
  // split must come from a parametric theory
  TheoryId tid = isParametric(t1) ? t1 : t2;
  if (!isParametric(tid))
  {
    return 0;
  }
  bool tcTermUnique = false;  // option
  if (tcTermUnique)
  {
    if (d_split_terms.find(a) != d_split_terms.end()
        || d_split_terms.find(b) != d_split_terms.end())
    {
      return 0;
    }
  }
  Node equality = a.eqNode(b);
  Node eqr = equality;
  bool tcRewUnique = false;  // option
  if (tcRewUnique)
  {
    eqr = Rewriter::rewrite(equality);
  }
  if (d_split_eq_rew.find(eqr) == d_split_eq_rew.end())
  {
    d_split_eq_rew.insert(eqr);
    if (tcTermUnique)
    {
      d_split_terms.insert(a);
      d_split_terms.insert(b);
    }
    // Assert(d_sharedTerms->isShared(a));
    // Assert(d_sharedTerms->isShared(b));
    Assert(!d_sharedTerms->isShared(a) || !d_sharedTerms->isShared(b)
           || (!d_sharedTerms->areEqual(a, b)
               && !d_sharedTerms->areDisequal(a, b)));
    Node split = equality.orNode(equality.notNode());
    sendLemma(split, tid);
    Node e = d_te.ensureLiteral(equality);
    d_te.getPropEngine()->requirePhase(e, true);
    Trace("tc-model-split")
        << "---> split on " << equality << ", theory = " << tid << std::endl;
    Trace("tc-model-debug") << "---> rewritten split : " << e << std::endl;
    return 1;
  }
  return 0;
}

class ModelTrie
{
 public:
  std::vector<Node> d_terms;
  std::vector<Node> d_values;
  std::map<Node, ModelTrie> d_children;

  void add(TheoryModel* m, Node n, std::vector<std::pair<Node, Node>>& cps)
  {
    Trace("tc-model-debug-mv") << "  evaluate " << n << " :: ";
    ModelTrie* mt = this;
    std::vector<Node> argvs;
    Trace("tc-model-debug-mv") << "( ";
    for (const Node& nc : n)
    {
      Node r = m->getRepresentative(nc);
      Trace("tc-model-debug-mv") << r << " ";
      argvs.push_back(r);
    }
    Trace("tc-model-debug-mv") << ")";
    Node val = m->getRepresentative(n);
    Trace("tc-model-debug-mv") << " = " << val << std::endl;

    for (unsigned i = 0, size = argvs.size(); i < size; i++)
    {
      mt = &mt->d_children[argvs[i]];
    }

    for (unsigned i = 0, size = mt->d_terms.size(); i < size; i++)
    {
      Node v = mt->d_values[i];
      if (v != val)
      {
        cps.push_back(std::pair<Node, Node>(mt->d_terms[i], n));
        Trace("tc-model-debug-mv") << "...conflict pair : " << n << " <> "
                                   << mt->d_terms[i] << std::endl;
      }
    }
    mt->d_terms.push_back(n);
    mt->d_values.push_back(val);
  }
};

void CombinationModelBased::combineTheoriesOld()
{
  Trace("combineTheories") << "CombinationModelBased::combineTheoriesOld()"
                           << std::endl;

  Trace("tc-model") << "------model-based theory combination" << std::endl;
  d_shared_terms_merge.clear();
  d_split_eq_rew.clear();
  d_split_terms.clear();
  d_sharedEq.clear();
  d_sharedDeq.clear();
  bool success = true;
  unsigned numSplits = 0;
  std::vector<std::pair<Node, Node>> conflict_pairs;
  std::map<Node, Node> value_to_rep;
  TheoryModel* m = getModel();
  if (d_mmanager->buildModel())
  {
    Trace("tc-model-debug")
        << "--- model was consistent, verifying..." << std::endl;

    std::map<Node, ModelTrie> model_trie;
    eq::EqualityEngine* ee = m->getEqualityEngine();
    Assert(ee->consistent());
    // map from equivalence classes to values
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
    while (!eqcs_i.isFinished())
    {
      TNode r = (*eqcs_i);
      Trace("tc-model-debug") << "model-verify: EQC : " << r << std::endl;
      Node rr = m->getRepresentative(r);
      Trace("tc-model-debug") << "              rep : " << rr << std::endl;
      std::map<Node, Node>::iterator itv = value_to_rep.find(rr);
      if (itv != value_to_rep.end())
      {
        Trace("tc-model-debug") << "Merge shared term eqc : " << itv->second
                                << " " << r << std::endl;
        // since these two equivalence classes were assigned the same value,
        // they are the same equivalence class, even though they have
        // not merged in the equality engine of the model.
        mergeSharedTermEqcs(itv->second, r);
        // cannot guarantee success
        success = false;
      }
      else
      {
        value_to_rep[rr] = r;
      }
      eq::EqClassIterator eqc_i = eq::EqClassIterator(r, ee);
      while (!eqc_i.isFinished())
      {
        TNode n = (*eqc_i);
        Trace("tc-model-debug2") << "  term " << n << std::endl;
        // check whether this is a parametric operator
        if (n.getKind() != kind::EQUAL && n.hasOperator())
        {
          TheoryId tid = Theory::theoryOf(n);
          if (isParametric(tid))
          {
            Node op = n.getOperator();
            model_trie[op].add(m, n, conflict_pairs);
          }
        }
        ++eqc_i;
      }
      ++eqcs_i;
    }
    if (success)
    {
      if (conflict_pairs.empty())
      {
        Trace("tc-model") << "--> model building succeeded" << std::endl;
      }
      else
      {
        success = false;
        Trace("tc-model")
            << "--> model was inconsistent during verification (by congruence)"
            << std::endl;
      }
    }
    else
    {
      Trace("tc-model")
          << "--> model was inconsistent during verification (by equality)"
          << std::endl;
    }

    if (!conflict_pairs.empty())
    {
      Trace("tc-model-debug") << "--------check " << conflict_pairs.size()
                              << " conflict pairs..." << std::endl;
      for (std::pair<Node, Node>& cp : conflict_pairs)
      {
        Node a = cp.first;
        Node b = cp.second;
        Trace("tc-model-debug")
            << "  check " << a << " <> " << b << "..." << std::endl;
        Assert(a.getNumChildren() == b.getNumChildren());
        Assert(a.getOperator() == b.getOperator());
        TheoryId parentId = Theory::theoryOf(a);
        bool useAckermann = false;  // option
        if (useAckermann)
        {
          std::vector<Node> lem_c;
          Node eq = a.eqNode(b);
          TheoryId tid = Theory::theoryOf(eq);
          lem_c.push_back(eq);
          for (unsigned i = 0, size = a.getNumChildren(); i < size; i++)
          {
            Node ac = a[i];
            Node bc = b[i];
            lem_c.push_back(ac.eqNode(bc).negate());
          }
          Node lem;
          if (lem_c.size() > 0)
          {
            lem = NodeManager::currentNM()->mkNode(kind::OR, lem_c);
          }
          else
          {
            lem = lem_c[0];
          }
          Trace("tc-model-split")
              << "Ackermanization lemma : " << lem << std::endl;
          sendLemma(lem, tid);
          numSplits++;
        }
        else
        {
          for (unsigned i = 0, size = a.getNumChildren(); i < size; i++)
          {
            Node ac = a[i];
            Node bc = b[i];
            if (ac != bc)
            {
              TheoryId childId = Theory::theoryOf(ac.getType());
              if (parentId != childId)
              {
                if (!d_sharedTerms->isShared(ac) || !d_sharedTerms->isShared(bc)
                    || (!d_sharedTerms->areEqual(ac, bc)
                        && !d_sharedTerms->areDisequal(ac, bc)))
                {
                  // check split immediately
                  numSplits += checkSplitCandidate(ac, bc, parentId, childId);
                }
              }
            }
          }
        }
      }
      Assert(numSplits > 0);
    }
  }
  else
  {
    // building was inconsistent (e.g. during collectModelInfo)
    success = false;
    Trace("tc-model") << "--> model failed during building" << std::endl;
    // we look at shared terms in same equivalence classes below
  }

  if (!success && numSplits == 0)
  {
    // get the shared terms for each theory
    std::map<TheoryId, std::unordered_set<TNode, TNodeHashFunction>> tshared;
    for (TheoryId theoryId = theory::THEORY_FIRST;
         theoryId != theory::THEORY_LAST;
         ++theoryId)
    {
      Theory* t = d_te.theoryOf(theoryId);
      if (t == nullptr)
      {
        continue;
      }
      tshared[theoryId] = t->currentlySharedTerms();
    }
    // it can happen that a shared term disequality was not propagated but set
    // true in the model
    Trace("tc-model-debug")
        << "--------check shared terms in same equivalence classes..."
        << std::endl;
    // for each equivalence class of the model containing 2+ non-propagated
    // equal shared terms
    Trace("tc-model-debug")
        << "Processing " << d_shared_terms_merge.size()
        << " equivalence classes with shared terms..." << std::endl;
    for (std::pair<const TNode, std::vector<TNode>>& p : d_shared_terms_merge)
    {
      if (p.second.size() > 1)
      {
        if (Trace.isOn("tc-model-debug"))
        {
          Trace("tc-model-debug")
              << "* Equivalence class " << p.first << " has " << p.second.size()
              << " shared terms : " << std::endl;
          for (unsigned i = 0, size = p.second.size(); i < size; i++)
          {
            Trace("tc-model-debug")
                << "  " << i << " : " << p.second[i] << std::endl;
          }
        }

        // for each theory
        for (std::pair<const TheoryId,
                       std::unordered_set<TNode, TNodeHashFunction>>& tts :
             tshared)
        {
          TheoryId tid = tts.first;
          bool tpar = isParametric(tid);

          // maintain the subset of p.second that is unique modulo equality
          // and shared with this theory
          std::vector<TNode> shared_eqc;

          // for each term in the equivalence class
          for (const TNode& b : p.second)
          {
            Assert(d_sharedTerms->isShared(b));

            // is b shared with this theory?
            if (tts.second.find(b) != tts.second.end())
            {
              // check each relevant previously processed term
              bool successPair = true;
              for (const TNode& a : shared_eqc)
              {
                numSplits += checkPair(a, b, tid, tpar);
                /*
                if (es==EQUALITY_TRUE || es==EQUALITY_TRUE_IN_MODEL)
                {
                  // don't consider 2+ terms that this theory thinks are equal
                  successPair = false;
                  break;
                }
                */
              }

              // add to shared_eqc if not equal to another previously seen
              // term
              if (successPair)
              {
                shared_eqc.push_back(b);
              }
            }
          }
        }
      }
    }
    numSplits = checkSharedTermMaps(tshared);
    if (numSplits == 0)
    {
      // verify the model?
    }

    if (numSplits > 0)
    {
      Trace("tc-model") << "--> combine theories produced " << numSplits
                        << " splits on shared terms." << std::endl;
    }
    else
    {
      Trace("tc-model") << "--> combine theories produced no splits"
                        << std::endl;
      Assert(false);
    }
  }
  Trace("tc-model") << "------end model-based theory combination" << std::endl;

  Trace("combineTheories")
      << "CombinationModelBased::combineTheoriesModelBased() : requested "
      << numSplits << " splits." << std::endl;
}

}  // namespace theory
}  // namespace CVC4
