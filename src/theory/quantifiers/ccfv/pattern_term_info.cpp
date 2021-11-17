/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Info per pattern term in CCFV.
 */

#include "theory/quantifiers/ccfv/pattern_term_info.h"

#include "expr/node_algorithm.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/ccfv/state.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

PatTermInfo::PatTermInfo(context::Context* c)
    : d_eq(c), d_numUnassigned(c, 0), d_parentNotify(c), d_parentCongNotify(c)
{
}

void PatTermInfo::initialize(TNode pattern, TermDb* tdb)
{
  d_pattern = pattern;
  d_isBooleanConnective =
      pattern.getKind() == EQUAL || expr::isBooleanConnective(pattern);
  if (!d_isBooleanConnective)
  {
    d_matchOp = tdb->getMatchOperator(pattern);
  }
}

void PatTermInfo::resetRound()
{
  d_eq = Node::null();
  if (d_isBooleanConnective)
  {
    /*
    for (TNode pc : pattern)
    {
      if (!expr::hasBoundVar(pc))
      {
        continue;
      }
      d_numUnassigned = d_numUnassigned + 1;
    }
    */
    // TODO: duplicate children?? should probably handle in rewriter
    // for quantifiers
    d_numUnassigned = d_pattern.getNumChildren();
  }
}

bool PatTermInfo::isActive() const { return d_eq.get().isNull(); }

bool PatTermInfo::notifyChild(State& s, TNode child, TNode val)
{
  Assert(!val.isNull());
  Assert(s.isGroundEqc(val) || s.isSink(val));
  if (!d_eq.get().isNull())
  {
    // already set
    return false;
  }
  if (d_isBooleanConnective)
  {
    Trace("ccfv-state-debug")
        << "Notify Bool connective: " << d_pattern << " child " << child
        << " == " << val << std::endl;
    // if a Boolean connective, handle short circuiting if we set a non-sink
    // value
    Kind k = d_pattern.getKind();
    if (!s.isSink(val))
    {
      // implies and xor are eliminated from quantifier bodies
      Assert(k != IMPLIES && k != XOR);
      if ((k == AND && !val.getConst<bool>())
          || (k == OR && val.getConst<bool>()))
      {
        // the value determines the value of this
        d_eq = val;
        Trace("ccfv-state-debug") << "...short circuit " << val << std::endl;
        return true;
      }
      if (k == ITE)
      {
        // if the condition is being set, and the branch already has a value,
        // then this has the value of the branch.
        if (d_pattern[0] == child)
        {
          bool pol = val.getConst<bool>();
          Node vbranch = s.getValue(d_pattern[pol ? 1 : 2]);
          if (!vbranch.isNull())
          {
            d_eq = vbranch;
            Trace("ccfv-state-debug")
                << "...branched to " << vbranch << std::endl;
            return true;
          }
        }
        else
        {
          // if the branch is being set, the condition is determined, and it is
          // the relevant branch, then this value is val.
          Node vcond = s.getValue(d_pattern[0]);
          if (!vcond.isNull() && vcond.isConst())
          {
            if (child == d_pattern[vcond.getConst<bool>() ? 1 : 2])
            {
              d_eq = val;
              Trace("ccfv-state-debug")
                  << "...relevant branch " << val << std::endl;
              return true;
            }
          }
        }
      }
    }
    else
    {
      if (k==EQUAL)
      {
        // sink on either side of equality is automatic sink
        d_eq = val;
        Trace("ccfv-state-debug") << "...sink equality" << std::endl;
        return true;
      }
    }
    // if a Boolean connective, we can possibly evaluate
    Assert(d_numUnassigned.get() > 0);
    d_numUnassigned = d_numUnassigned.get() - 1;
    Trace("ccfv-state-debug")
        << "...unassigned children now " << d_numUnassigned << std::endl;
    if (d_numUnassigned == 0)
    {
      // set to unknown, handle cases
      d_eq = s.getSink();
      NodeManager* nm = NodeManager::currentNM();
      Kind k = d_pattern.getKind();
      Assert(k != IMPLIES && k != XOR);
      if (k == AND || k == OR)
      {
        for (TNode pc : d_pattern)
        {
          TNode cvalue = s.getValue(pc);
          if (s.isSink(cvalue))
          {
            // unknown, we are done
            Trace("ccfv-state-debug") << "...unknown child of AND/OR" << std::endl;
            return true;
          }
        }
        d_eq = nm->mkConst(k == AND);
        Trace("ccfv-state-debug") << "...exhausted AND/OR" << std::endl;
      }
      else
      {
        TNode cval1 = s.getValue(d_pattern[0]);
        Assert(!cval1.isNull());
        Assert(!d_pattern[0].getType().isBoolean() || cval1.isConst() || isSink(cval1));
        if (k == NOT)
        {
          if (cval1.isConst())
          {
            d_eq = nm->mkConst(!cval1.getConst<bool>());
            Trace("ccfv-state-debug") << "...eval negation " << d_eq.get() << std::endl;
          }
        }
        else if (k == ITE)
        {
          if (cval1.isConst())
          {
            // if condition evaluates, get value of branch
            d_eq = s.getValue(d_pattern[cval1.getConst<bool>() ? 1 : 2]);
            Trace("ccfv-state-debug") << "...take branch " << d_eq.get() << std::endl;
          }
          else
          {
            // otherwise, we only are known if the branches are equal
            TNode cval2 = s.getValue(d_pattern[1]);
            Assert(!cval2.isNull());
            // this handles any type ITE
            if (!s.isSink(cval1) && cval2 == s.getValue(d_pattern[2]))
            {
              d_eq = cval2;
              Trace("ccfv-state-debug") << "...equal branches " << cval2 << std::endl;
            }
          }
        }
        else
        {
          Assert(k == EQUAL);
          // this handles any type EQUAL. If either side is sink, we are sink.
          // Otherwise, we handle cases below.
          if (!s.isSink(cval1))
          {
            TNode cval2 = s.getValue(d_pattern[1]);
            Assert(!cval2.isNull());
            if (!s.isSink(cval2))
            {
              // if both side evaluate, we evaluate to true if both sides are
              // equal, false the values are disequal (which includes checking
              // if cval1 and cval2 are distinct constants), and do not evaluate
              // otherwise.
              if (cval1 == cval2)
              {
                d_eq = nm->mkConst(true);
                Trace("ccfv-state-debug") << "...equal via " << cval1 << std::endl;
              }
              else if (s.areDisequal(cval1, cval2))
              {
                Trace("ccfv-state-debug") << "...disequal " << cval1 << " != " << cval2 << std::endl;
                d_eq = nm->mkConst(false);
              }
              else
              {
                Trace("ccfv-state-debug") << "...unknown equal" << std::endl;
                // otherwise we don't evaluate. Notice that equalities are
                // not marked as final terms, and thus this equality will be
                // active but unassigned. This is different from marking
                // it as "sink", since we want to propagate equalities between
                // known terms. Notice that Booleans require being assigned to
                // constants, so this only applies to non-Boolean equalities.
                Assert (!val.isBoolean());
                d_eq = Node::null();
                return false;
              }
            }
          }
        }
      }
      return true;
    }
  }
  else
  {
    // for congruence terms
    // if the value of a child is unknown, we are now unknown
    if (s.isSink(val))
    {
      d_eq = val;
      return true;
    }
  }
  return false;
}

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
