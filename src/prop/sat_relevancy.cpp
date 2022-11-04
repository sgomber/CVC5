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
#include "theory/theory_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace prop {

RlvProperty operator|(RlvProperty lhs, RlvProperty rhs)
{
  return static_cast<RlvProperty>(static_cast<uint32_t>(lhs)
                                  | static_cast<uint32_t>(rhs));
}
RlvProperty& operator|=(RlvProperty& lhs, RlvProperty rhs)
{
  lhs = lhs | rhs;
  return lhs;
}
RlvProperty operator&(RlvProperty lhs, RlvProperty rhs)
{
  return static_cast<RlvProperty>(static_cast<uint32_t>(lhs)
                                  & static_cast<uint32_t>(rhs));
}
RlvProperty& operator&=(RlvProperty& lhs, RlvProperty rhs)
{
  lhs = lhs & rhs;
  return lhs;
}

RlvInfo::RlvInfo(context::Context* context)
    : d_parents(context),
      d_parentPol(context),
      d_childPol(context),
      d_rlvp(context, RlvProperty::NONE)
{
}
bool RlvInfo::isRelevant(bool pol) const
{
  return (d_rlvp.get() & (pol ? RlvProperty::RLV_POS : RlvProperty::RLV_NEG))
         != RlvProperty::NONE;
}

bool RlvInfo::isRelevant() const
{
  return (d_rlvp.get() & (RlvProperty::RLV_POS | RlvProperty::RLV_NEG))
         != RlvProperty::NONE;
}

void RlvInfo::setRelevant(bool pol)
{
  d_rlvp.set(d_rlvp.get()
             | (pol ? RlvProperty::RLV_POS : RlvProperty::RLV_NEG));
}

bool RlvInfo::isEnqueued() const
{
  return (d_rlvp.get() & RlvProperty::ENQUEUED) != RlvProperty::NONE;
}
void RlvInfo::setEnqueued()
{
  d_rlvp.set(d_rlvp.get() | RlvProperty::ENQUEUED);
}
bool RlvInfo::isJustified() const
{
  return (d_rlvp.get() & RlvProperty::JUSTIFIED) != RlvProperty::NONE;
}
void RlvInfo::setJustified()
{
  d_rlvp.set(d_rlvp.get() | RlvProperty::JUSTIFIED);
}
bool RlvInfo::isInput(bool& pol) const
{
  if ((d_rlvp.get() & RlvProperty::INPUT_POS) != RlvProperty::NONE)
  {
    pol = true;
    return true;
  }
  else if ((d_rlvp.get() & RlvProperty::INPUT_NEG) != RlvProperty::NONE)
  {
    pol = false;
    return true;
  }
  return false;
}
void RlvInfo::setInput(bool pol)
{
  d_rlvp.set(d_rlvp.get()
             | (pol ? RlvProperty::INPUT_POS : RlvProperty::INPUT_NEG));
}

bool RlvInfo::isPreregistered() const
{
  return (d_rlvp.get() & RlvProperty::PREREG) != RlvProperty::NONE;
}
void RlvInfo::setPreregistered()
{
  d_rlvp.set(d_rlvp.get() | RlvProperty::PREREG);
}

bool RlvInfo::isAsserted(bool& pol) const
{
  if ((d_rlvp.get() & RlvProperty::ASSERTED_POS) != RlvProperty::NONE)
  {
    pol = true;
    return true;
  }
  else if ((d_rlvp.get() & RlvProperty::ASSERTED_NEG) != RlvProperty::NONE)
  {
    pol = false;
    return true;
  }
  return false;
}

void RlvInfo::setAsserted(bool pol)
{
  d_rlvp.set(d_rlvp.get()
             | (pol ? RlvProperty::ASSERTED_POS : RlvProperty::ASSERTED_NEG));
}

bool RlvInfo::isMarkedPreregistered() const
{
  return (d_rlvp.get() & RlvProperty::MARKED_PREREG) != RlvProperty::NONE;
}
void RlvInfo::setMarkedPreregistered()
{
  d_rlvp.set(d_rlvp.get() | RlvProperty::MARKED_PREREG);
}

SatRelevancy::SatRelevancy(CDCLTSatSolverInterface* satSolver,
                           TheoryEngine* theoryEngine,
                           Env& env,
                           CnfStream* cnfStream,
                           options::SatRelevancyMode mode)
    : EnvObj(env),
      d_satSolver(satSolver),
      d_theoryEngine(theoryEngine),
      d_cnfStream(cnfStream),
      d_inputs(env.getUserContext()),
      d_numInputs(env.getContext(), 0),
      d_rlvMap(env.getContext()),
      d_numAsserts(env.getContext(), 0),
      d_numAssertsEnq(env.getContext(), 0),
      d_numAssertsRlv(env.getContext(), 0),
      d_numAssertsPrereg(env.getContext(), 0),
      d_mode(mode)
{
  // temporary
  d_isActiveTmp = true;
}

SatRelevancy::~SatRelevancy() {}

void SatRelevancy::presolve(context::CDQueue<TNode>& queue)
{
  // ensure lemmas are relevant here, which is a minor optimization to ensure
  // we don't have to refresh them at decision level != 0
  // TODO: is this necessary?
  ensureLemmasRelevant(&queue);
}

void SatRelevancy::notifyLemma(TNode lem, context::CDQueue<TNode>& queue)
{
  // relevancy is SAT-context dependent, need to double check lemmas
  // when we backtrack
  Trace("sat-rlv") << "notifyLemma: " << lem << std::endl;
  /*
  if (lem.isConst())
  {
    // ignore true/false
    return;
  }
  */
  d_inputs.push_back(lem);
  Trace("sat-rlv") << "notifyLemma: finished" << std::endl;
}

void SatRelevancy::notifyActivatedSkolemDefs(const std::vector<TNode>& defs,
                                             context::CDQueue<TNode>& queue)
{
  Trace("sat-rlv") << "notifyActivatedSkolemDefs " << std::endl;
  // set the lemma is currently relevant
  for (TNode n : defs)
  {
    setRelevant(n, true, &queue);
  }
  Trace("sat-rlv") << "notifyActivatedSkolemDef: finished" << std::endl;
}

void SatRelevancy::notifyDecisionRequest(TNode n,
                                         context::CDQueue<TNode>& queue)
{
  Trace("sat-rlv") << "notifyDecisionRequest: " << n << std::endl;
  // set the literal is currently relevant
  setRelevant(n, true, &queue);
  Trace("sat-rlv") << "notifyDecisionRequest: finished" << std::endl;
}

void SatRelevancy::notifyAsserted(const SatLiteral& l,
                                  context::CDQueue<TNode>& queue)
{
  TNode n = d_cnfStream->getNode(l);
  Trace("sat-rlv") << "notifyAsserted: " << n << std::endl;
  if (!d_isActiveTmp)
  {
    queue.push(n);
  }
  bool pol = n.getKind() != NOT;
  TNode atom = pol ? n : n[0];
  // first, look at wait lists
  RlvInfo* ri = getOrMkRlvInfo(atom);
  // we are going to iterate through each parent that is waiting
  // on its value and possibly make this assertion relevant (when nrlv=true)
  bool nrlv = false;
  Assert(ri->d_parents.size() == ri->d_childPol.size());
  for (size_t i = 0, nparents = ri->d_parents.size(); i < nparents; i++)
  {
    TNode parent = ri->d_parents[i];
    bool ppol = ri->d_parentPol[i];
    bool cpol = ri->d_childPol[i];
    Trace("sat-rlv-debug") << "  look at parent: " << parent
                           << ", cpol=" << cpol << std::endl;
    // n makes a child of parent have value equal to (pol==cpol), where pol
    // is the assigned value of the atom, and cpol is its polarity in the
    // parent. For instance, (and (not A) B), when A is assigned true, we
    // get that pol=true, cpol = false, and hence we notify that a child of
    // AND is false.
    if (setAssertedChild(atom, pol == cpol, parent, ppol, queue))
    {
      Trace("sat-rlv-debug") << "  ...now relevant" << std::endl;
      // due to the above call, n is now relevant
      nrlv = true;
    }
  }

  // note that notify formulas are in terms of atoms
  if (!d_cnfStream->isNotifyFormula(atom))
  {
    d_numAsserts.set(d_numAsserts + 1);

    // we are a theory literal
    // if we became relevant due to a parent, or are already relevant, enqueue
    if (nrlv || ri->isRelevant(pol))
    {
      // preregister if not done already
      preregister(atom, ri);
      // then, enqueue
      enqueue(n, false, ri, &queue);
    }
    else
    {
      // Not currently necessary, since we use the prop engine to look up values
      // set asserted
      // ri->setAsserted(pol);
    }
    // otherwise we will assert if the literal gets marked as relevant
  }
  else
  {
    // mark as asserted
    // ri->setAsserted(pol);
    // if now relevant
    if (nrlv)
    {
      // this formula is now relevant and is not a theory atom
      setRelevantInternal(atom, pol, &queue, ri);
    }
  }
  Trace("sat-rlv") << "notifyAsserted: finished" << std::endl;
}

void SatRelevancy::setRelevant(
    TNode n, bool pol, context::CDQueue<TNode>* queue, RlvInfo* ri, bool input)
{
  if (n.getKind() == NOT)
  {
    pol = !pol;
    n = n[0];
  }
  setRelevantInternal(n, pol, queue, ri, input);
}

void SatRelevancy::setRelevantInternal(TNode atom,
                                       bool pol,
                                       context::CDQueue<TNode>* queue,
                                       RlvInfo* ri,
                                       bool input)
{
  if (ri == nullptr)
  {
    ri = getOrMkRlvInfo(atom);
  }
  if (ri->isRelevant(pol))
  {
    // already marked relevant
    return;
  }
  Trace("sat-rlv") << "- set relevant: " << atom << ", pol = " << pol
                   << std::endl;
  ri->setRelevant(pol);
  Assert(atom.getKind() != NOT);
  // notify formulas are in terms of atoms
  // NOTE this could be avoided by simply looking at the kind?
  if (d_cnfStream->isNotifyFormula(atom))
  {
    Trace("sat-rlv-debug") << "  ...a notify formula" << std::endl;
    switch (atom.getKind())
    {
      case AND:
      case OR:
      {
        if (pol == (atom.getKind() == AND))
        {
          // all children are immediately relevant
          for (TNode ac : atom)
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
          std::vector<TNode> acb;
          for (TNode ac : atom)
          {
            if (hasSatValue(ac, value))
            {
              if (value == pol)
              {
                // the value of the child justifies the node, we mark it as
                // relevant and are done. Notice the polarity (pol) is important
                //   ac = false justifies an AND parent being false,
                //   ac = true justifies an OR parent being true.
                Trace("sat-rlv-debug")
                    << "  ...justified already by " << ac << std::endl;
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
            for (TNode ac : acb)
            {
              addParentRlvWait(ac, true, atom, pol);
            }
          }
        }
      }
      break;
      case IMPLIES:
      {
        if (!pol)
        {
          // children are immediately relevant
          setRelevant(atom[0], true, queue);
          setRelevant(atom[1], false, queue);
        }
        else
        {
          // The first asserted child is relevant. Maybe a child is already
          // asserted?
          bool justified = false;
          bool value;
          std::vector<TNode> acb;
          std::vector<size_t> acbi;
          for (size_t i = 0; i < 2; i++)
          {
            TNode ac = atom[i];
            if (hasSatValue(ac, value))
            {
              // does the child make the IMPLIES true?
              if (value == (i == 1))
              {
                Trace("sat-rlv-debug")
                    << "  ...justified already by " << ac << std::endl;
                setRelevant(ac, value, queue);
                justified = true;
                break;
              }
            }
            else
            {
              acb.push_back(ac);
              acbi.push_back(i);
            }
          }
          // no children are asserted with the desired value, we are waiting for
          // the values for those that do no yet have values
          if (!justified)
          {
            // for all children that do not yet have values
            for (size_t i = 0, acbs = acb.size(); i < acbs; i++)
            {
              addParentRlvWait(acb[i], acbi[i] == 1, atom, pol);
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
          addParentRlvWait(atom[0], true, atom, pol);
        }
      }
      break;
      case EQUAL:
      case XOR:
      {
        Assert(atom.getNumChildren() == 2);
        // notify formulas of kind EQUAL should only be Boolean (IFF)
        Assert(atom[0].getType().isBoolean());
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
            addParentRlvWait(atom[i], true, atom, pol);
          }
        }
      }
      break;
      default:
      {
        // should be a variable
        Assert(atom.isVar())
            << "SatRelevancy::setRelevant: unexpected notify formula " << atom;
      }
      break;
    }
    return;
  }
  Trace("sat-rlv-debug") << "  ...not a notify formula" << std::endl;
  // preregister the atom here
  preregister(atom, ri);
  // if there is no queue, we are asserting that an input assertion is relevant,
  // it will be asserted anyways.
  Assert(queue != nullptr);
  // otherwise it is a theory literal, if it already has a SAT value, it should
  // be asserted now
  bool hasValue;
  bool value;
#ifdef USE_ASSERT_MARKS
  hasValue = ri->isAsserted(value);
#else
  if (input)
  {
    // The caller indicated that this is an input formula. It is important that
    // we don't call hasSatValue below, as input formulas do not necessarily
    // have literals in the SAT solver, as CNF conversion does not require this.
    ri->setInput(pol);
    value = pol;
    hasValue = true;
  }
  else if (ri->isInput(value))
  {
    // We have previously been marked as an input formula, we cannot call
    // hasSatValue below, for the same reasons. The value is computed by the
    // call to ri->isInput.
    hasValue = true;
  }
  else
  {
    hasValue = hasSatValue(atom, value);
  }
#endif
  // do we already have a value?
  if (hasValue)
  {
    // if so, enqueue the atom, possibly negated
    enqueue(atom, !value, ri, queue);
  }
}

bool SatRelevancy::hasSatValue(TNode node, bool& value)
{
#ifdef USE_ASSERT_MARKS
  // TODO: could use explicit assertion tracking here

  bool pol = node.getKind() != NOT;
  TNode atom = pol ? node : node[0];
  // TODO: pass ri
  RlvInfo* ri = getOrMkRlvInfo(atom);
  if (ri->isAsserted(value))
  {
    value = (value == pol);
    return true;
  }
  return false;
#endif

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

void SatRelevancy::addParentRlvWait(TNode n,
                                    bool pol,
                                    TNode parentAtom,
                                    bool ppol)
{
  if (n.getKind() == NOT)
  {
    pol = !pol;
    n = n[0];
  }
  RlvInfo* rwi = getOrMkRlvInfo(n);
  rwi->d_parents.push_back(parentAtom);
  rwi->d_parentPol.push_back(ppol);
  rwi->d_childPol.push_back(pol);
  Trace("sat-rlv-debug") << "  ...add parent rlv wait: " << n << " -> "
                         << parentAtom << ", ppol=" << ppol << std::endl;
}

RlvInfo* SatRelevancy::getOrMkRlvInfo(TNode n)
{
  RlvMap::const_iterator it = d_rlvMap.find(n);
  if (it != d_rlvMap.end())
  {
    return it->second.get();
  }
  std::shared_ptr<RlvInfo> rwi = std::make_shared<RlvInfo>(d_env.getContext());
  d_rlvMap.insert(n, rwi);
  return rwi.get();
}

bool SatRelevancy::setAssertedChild(TNode atom,
                                    bool pol,
                                    TNode parentAtom,
                                    bool ppol,
                                    context::CDQueue<TNode>& queue)
{
  Trace("sat-rlv-debug") << "setAssertedChild " << pol << " in " << parentAtom
                         << " with ppol=" << ppol << ", from " << atom
                         << std::endl;
  switch (parentAtom.getKind())
  {
    case AND:
    case OR:
    case IMPLIES:
    {
      Assert(ppol == (parentAtom.getKind() != AND));
      RlvInfo* pri = getOrMkRlvInfo(parentAtom);
      if (pri->isJustified())
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
        pri->setJustified();
        // the value of this is relevant
        return true;
      }
      // otherwise the value of this is not relevant
    }
    break;
    case ITE:
    {
      // ITE's only wait on their condition, so we know the condition was
      // asserted.
      // now set the proper branch to be relevant with the parent's polarity
      setRelevant(parentAtom[pol ? 1 : 2], ppol, &queue);
      // the value of this is now also relevant
      return true;
    }
    break;
    case EQUAL:
    case XOR:
    {
      // the value of the other side is now relevant, check both sides to
      // infer which side atom is on
      for (size_t i = 0; i < 2; i++)
      {
        TNode pc = parentAtom[i];
        TNode pcatom = pc.getKind() == NOT ? pc[0] : pc;
        if (pcatom == atom)
        {
          // the other side is relevant with a computed polarity
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
          << parentAtom;
    }
    break;
  }
  return false;
}

void SatRelevancy::ensureLemmasRelevant(context::CDQueue<TNode>* queue)
{
  // Here, we ensure that lemmas have been marked relevant. This is necessary
  // since lemmas persist in user contexts, but relevancy information is
  // SAT-context dependent. Thus, relevancy information for lemmas must be
  // refreshsed here when we backtrack.
  size_t index = d_numInputs.get();
  size_t numInputs = d_inputs.size();
  if (index >= numInputs)
  {
    return;
  }
  Trace("sat-rlv") << "ensureLemmasRelevant" << std::endl;
  while (index < numInputs)
  {
    TNode lem = d_inputs[index];
    Trace("sat-rlv") << "ensureLemmaRelevant: " << lem << std::endl;
    setRelevant(lem, true, queue, nullptr, true);
    index++;
  }
  Trace("sat-rlv") << "...finished ensureLemmasRelevant" << std::endl;
  d_numInputs = numInputs;
}

void SatRelevancy::check(theory::Theory::Effort effort,
                         context::CDQueue<TNode>& queue)
{
  ensureLemmasRelevant(&queue);
  if (TraceIsOn("sat-rlv-summary"))
  {
    if (theory::Theory::fullEffort(effort))
    {
      // d_numAssertsEnq.get()==d_numAssertsRlv.get() when --sat-rlv=all
      Trace("sat-rlv-summary")
          << "SatRelevancy::check(" << effort << "): " << d_numAssertsEnq.get()
          << "/" << d_numAsserts.get() << " assertions enqueued, "
          << d_numAssertsRlv.get() << "/" << d_numAssertsPrereg.get()
          << " preregistered" << std::endl;
    }
  }
}
void SatRelevancy::notifyVarNotify(TNode n)
{
  // do not distinguish var-notify from preregister
  notifyPrereg(n);
  /*
  RlvInfo* ri = getOrMkRlvInfo(n);
  ri->setMarkedPreregistered();
  ri->setPreregistered();
  // always preregister here?
  Trace("sat-rlv") << "*** var notify / preregister " << n << std::endl;
  d_theoryEngine->preRegister(n);
  */
}

void SatRelevancy::notifyPrereg(TNode n)
{
  // TEMPORARY
  RlvInfo* ri = getOrMkRlvInfo(n);
  ri->setMarkedPreregistered();
  Trace("sat-rlv") << "notifyPrereg: " << n << std::endl;
  d_numAssertsPrereg.set(d_numAssertsPrereg + 1);
  // always preregister immediately if already relevant
  if (ri->isRelevant() || d_mode != options::SatRelevancyMode::ALL)
  {
    Trace("sat-rlv") << "*** preregister " << n << std::endl;
    ri->setPreregistered();
    d_numAssertsRlv.set(d_numAssertsRlv + 1);
    d_theoryEngine->preRegister(n);
  }
  AlwaysAssert(n.getKind() != NOT);
}

void SatRelevancy::notifyPropagate(TNode n)
{
  /*
  Trace("sat-rlv") << "notifyPropagate: " << n << std::endl;
  TNode atom = n.getKind() == NOT ? n[0] : n;
  RlvInfo* ri = getOrMkRlvInfo(atom);
  AlwaysAssert(ri->isMarkedPreregistered())
      << "propagate before marked preregister";
  // AlwaysAssert(ri->isPreregistered()) << "propagate before preregister";
  if (!ri->isPreregistered())
  {
    Trace("sat-rlv-warn") << "WARN: propagate before preregister " << n
                          << std::endl;
  }
  // AlwaysAssert(!ri->isEnqueued()) << "propagate after enqueued";
  */
}

void SatRelevancy::preregister(TNode atom, RlvInfo* ri)
{
  if (!ri->isPreregistered())
  {
    if (d_mode == options::SatRelevancyMode::ALL)
    {
      AlwaysAssert(ri->isMarkedPreregistered())
          << "preregistering non-marked " << atom;
      Trace("sat-rlv") << "*** preregister " << atom << std::endl;
      ri->setPreregistered();
      d_numAssertsRlv.set(d_numAssertsRlv + 1);
      d_theoryEngine->preRegister(atom);
    }
  }
}

void SatRelevancy::enqueue(TNode atom,
                           bool negated,
                           RlvInfo* ri,
                           context::CDQueue<TNode>* queue)
{
  if (!ri->isEnqueued())
  {
    Trace("sat-rlv") << "*** enqueue " << atom << ", negated=" << negated
                     << std::endl;
    AlwaysAssert(ri->isMarkedPreregistered())
        << "enqueuing non-marked " << atom;
    //    bool avalue;
    // AlwaysAssert(ri->isAsserted(avalue))
    //    << "enqueuing non-asserted " << atom;
    if (d_isActiveTmp)
    {
      queue->push(negated ? atom.notNode() : Node(atom));
    }
    ri->setEnqueued();
    d_numAssertsEnq.set(d_numAssertsEnq + 1);
  }
}

}  // namespace prop
}  // namespace cvc5
