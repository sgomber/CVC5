/*********************                                                        */
/*! \file sat_relevancy.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sat relevancy module
 **/

#include "prop/sat_relevancy.h"

#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "prop/sat_solver.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace prop {

SatRelevancy::SatRelevancy(CDCLTSatSolverInterface* satSolver,
                           context::Context* context,
                           CnfStream* cnfStream)
    : d_satSolver(satSolver),
      d_context(context),
      d_cnfStream(cnfStream),
      d_rlv(context),
      d_justify(context),
      d_rlvWaitMap(context)
{
  // FIXME
  d_isActive = false;
}

SatRelevancy::~SatRelevancy() {}

void SatRelevancy::notifyPreprocessedAssertion(TNode a)
{
  // Mark each assertion as relevant. Notice we use a null queue since nothing
  // should have SAT values yet.
  Trace("sat-rlv") << "notifyPreprocessedAssertion: " << a << std::endl;
  setRelevant(a, nullptr);
}

void SatRelevancy::notifyNewLemma(TNode n, context::CDQueue<TNode>& queue)
{
  Trace("sat-rlv") << "notifyNewLemma: " << n << std::endl;
  // set the lemma is relevant
  setRelevant(n, &queue);
}

void SatRelevancy::notifyAsserted(const SatLiteral& l,
                                  context::CDQueue<TNode>& queue)
{
  Node n = d_cnfStream->getNode(l);
  Trace("sat-rlv") << "notifyAsserted: " << n << std::endl;
  bool pol = n.getKind() != NOT;
  TNode atom = pol ? n : n[0];
  // first, look at wait lists
  RlvWaitMap::const_iterator it = d_rlvWaitMap.find(atom);
  if (it == d_rlvWaitMap.end())
  {
    // nothing is waiting on its value, we are done.
    return;
  }
  // otherwise, we are going to iterate through each parent that is waiting
  // on its value and possibly update relevancy
  RlvWaitInfo* rwi = it->second.get();
  bool nrlv = false;
  Assert(rwi->d_parents.size() == rwi->d_childPol.size());
  for (size_t i = 0, nparents = rwi->d_parents.size(); i < nparents; i++)
  {
    TNode parent = rwi->d_parents[i];
    bool cpol = rwi->d_childPol[i];
    // n makes a child of parent have value equal to (pol==cpol), where pol
    // is the assigned value of the atom, and cpol is its polarity in the
    // parent. For instance, (and (not A) B), when A is assigned true, we
    // get that pol=true, cpol = false, and hence we notify that a child of
    // AND is false.
    if (setAssertedChild(atom, pol == cpol, parent, queue))
    {
      // due to the above call, n is now relevant
      nrlv = true;
    }
  }
  // note that notify formulas are in terms of atoms
  if (!d_cnfStream->isNotifyFormula(atom))
  {
    // we are a theory literal
    // if we became relevant due to a parent, or are already relevant, enqueue
    if (nrlv || d_rlv.find(n) != d_rlv.end())
    {
      Trace("sat-rlv-debug") << "- enqueue from assert " << n << std::endl;
      if (d_isActive)
      {
        queue.push(n);
      }
    }
    // otherwise we will assert if the literal gets marked as relevant
  }
  else if (nrlv)
  {
    // based on parents, this formula is now relevant and is not a theory atom
    setRelevant(n, &queue);
  }
  Trace("sat-rlv") << "...finished" << std::endl;
  if (!d_isActive)
  {
    queue.push(n);
  }
}

void SatRelevancy::setRelevant(TNode n, context::CDQueue<TNode>* queue)
{
  if (d_rlv.find(n) != d_rlv.end())
  {
    // already marked relevant
    return;
  }
  Trace("sat-rlv") << "- set relevant: " << n << std::endl;
  d_rlv.insert(n);
  bool pol = n.getKind() != NOT;
  TNode atom = pol ? n : n[0];
  Assert(atom.getKind() != NOT);
  // notify formulas are in terms of atoms
  // NOTE this could be avoided by simply looking at the kind?
  if (d_cnfStream->isNotifyFormula(atom))
  {
    switch (atom.getKind())
    {
      case AND:
      case OR:
      {
        if (pol == (atom.getKind() == AND))
        {
          // all children are immediately relevant
          for (const Node& ac : atom)
          {
            setRelevant(ac, pol, queue);
          }
        }
        else
        {
          // The first asserted child is relevant. Maybe a child is already
          // asserted?
          bool justified = false;
          bool value;
          std::vector<Node> acb;
          for (const Node& ac : atom)
          {
            if (hasSatValue(ac, value))
            {
              if (value == pol)
              {
                // the value of the child justifies the node, we mark it as
                // relevant and are done. Notice the polarity (pol) is important
                //   ac = false justifies an AND parent being false,
                //   ac = true justifies an OR parent being true.
                setRelevant(ac, pol, queue);
                justified = true;
                break;
              }
            }
            else
            {
              acb.push_back(ac);
            }
          }
          // no children are asserted with the desired value, we are waiting for
          // the values for those that do no yet have values
          if (!justified)
          {
            // for all children that do not yet have values
            for (const Node& ac : acb)
            {
              addParentRlvWait(ac, n);
            }
          }
        }
      }
      break;
      case ITE:
      {
        // Based on the asserted value of the condition, one branch becomes
        // relevant. Maybe the condition is already asserted?
        bool value;
        Assert(atom[0].getKind() != NOT);
        if (hasSatValue(atom[0], value))
        {
          // the condition's value is relevant
          setRelevant(atom[0], value, queue);
          // the proper branch, with the proper polarity, is also relevant
          setRelevant(atom[value ? 1 : 2], pol, queue);
        }
        else
        {
          // otherwise, we are waiting for the value of the condition
          addParentRlvWait(atom[0], n);
        }
      }
      break;
      case EQUAL:
      case XOR:
      {
        Assert(atom.getNumChildren() == 2);
        // do we have values for either of the children?
        bool value;
        if (hasSatValue(atom[0], value))
        {
          setRelevant(atom[0], value, queue);
          // atom[1] is also relevant with the proper polarity
          setRelevant(
              atom[1], value == (pol == (atom.getKind() == EQUAL)), queue);
        }
        else if (hasSatValue(atom[1], value))
        {
          setRelevant(atom[1], value, queue);
          // atom[0] is also relevant with the proper polarity
          setRelevant(
              atom[0], value == (pol == (atom.getKind() == EQUAL)), queue);
        }
        else
        {
          // neither have values, we are waiting
          for (size_t i = 0; i < 2; i++)
          {
            addParentRlvWait(atom[i], n);
          }
        }
      }
      break;
      default:
      {
        // should be a variable
        Assert(atom.isVar())
            << "SatRelevancy::setRelevant: unexpected notify formula " << n;
      }
      break;
    }
    return;
  }

  // otherwise it is a theory literal, if it already has a SAT value, it should
  // be asserted now
  bool value;
  if (hasSatValue(atom, value))
  {
    // now, enqueue it
    Assert(queue != nullptr);
    Node alit = value ? Node(atom) : atom.notNode();
    Trace("sat-rlv-debug") << "- enqueue " << alit << std::endl;
    if (d_isActive)
    {
      queue->push(alit);
    }
  }
}

void SatRelevancy::setRelevant(TNode n,
                               bool pol,
                               context::CDQueue<TNode>* queue)
{
  Node np = pol ? Node(n) : n.negate();
  setRelevant(np, queue);
}

bool SatRelevancy::hasSatValue(TNode node, bool& value) const
{
  SatLiteral lit = d_cnfStream->getLiteral(node);
  SatValue v = d_satSolver->value(lit);
  if (v == SAT_VALUE_TRUE)
  {
    value = true;
    return true;
  }
  else if (v == SAT_VALUE_FALSE)
  {
    value = false;
    return true;
  }
  Assert(v == SAT_VALUE_UNKNOWN);
  return false;
}

void SatRelevancy::addParentRlvWait(TNode n, TNode parent)
{
  bool pol = n.getKind() != NOT;
  TNode atom = pol ? n : n[0];
  RlvWaitMap::const_iterator it = d_rlvWaitMap.find(atom);
  std::shared_ptr<RlvWaitInfo> rwi;
  if (it != d_rlvWaitMap.end())
  {
    rwi = it->second;
  }
  else
  {
    rwi = std::make_shared<RlvWaitInfo>(d_context);
    d_rlvWaitMap.insert(n, rwi);
  }
  rwi->d_parents.push_back(parent);
  rwi->d_childPol.push_back(pol);
  Trace("sat-rlv") << "- add parent rlv wait: " << n << " -> " << parent
                   << std::endl;
}

bool SatRelevancy::setAssertedChild(TNode atom,
                                    bool pol,
                                    TNode parent,
                                    context::CDQueue<TNode>& queue)
{
  Trace("sat-rlv-debug") << "setAssertedChild " << pol << " in " << parent
                         << ", from " << atom << std::endl;
  bool ppol = parent.getKind() == NOT;
  TNode parentAtom = ppol ? parent : parent[0];
  switch (parentAtom.getKind())
  {
    case AND:
    case OR:
    {
      Assert(ppol == (parentAtom.getKind() == OR));
      if (d_justify.find(parent) != d_justify.end())
      {
        Trace("sat-rlv-debug") << "...already justified" << std::endl;
        // the parent was already justified by another child, nothing to do
        return false;
      }
      // does it make the parent true?
      if (pol == ppol)
      {
        Trace("sat-rlv-debug") << "...now justified" << std::endl;
        // we've justified the parent
        d_justify.insert(parent);
        // the value of this is relevant
        return true;
      }
      // otherwise the value of this is not relevant
    }
    break;
    case ITE:
    {
      // now set the proper branch to be relevant with the parent's polarity
      setRelevant(parentAtom[pol ? 1 : 2], ppol, &queue);
      // the value of this is now also relevant
      return true;
    }
    break;
    case EQUAL:
    case XOR:
    {
      // the value of the other side is now relevant
      for (size_t i = 0; i < 2; i++)
      {
        TNode pc = parentAtom[i];
        TNode pcatom = pc.getKind() == NOT ? pc[0] : pc;
        if (pcatom == atom)
        {
          setRelevant(parentAtom[1 - i],
                      pol == (ppol == (parentAtom.getKind() == EQUAL)),
                      &queue);
          break;
        }
      }
      // the value of this is now also relevant
      return true;
    }
    break;
    default:
    {
      Unhandled()
          << "SatRelevancy::setAssertedChild: unexpected parent formula "
          << parent;
    }
    break;
  }
  return false;
}

}  // namespace prop
}  // namespace CVC4
