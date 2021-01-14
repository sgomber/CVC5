/*********************                                                        */
/*! \file eqc_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of equivalence class info for the theory of strings
 **/

#include "theory/strings/eqc_info.h"

#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "theory/rewriter.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {
  
CExp::CExp(context::Context* c) : d_t(c), d_c(c), d_exp(c)
{
}
bool CExp::isNull() const { return d_t.get().isNull(); }

EqcInfo::EqcInfo(context::Context* c)
    : d_lengthTerm(c),
      d_codeTerm(c),
      d_cardinalityLemK(c),
      d_normalizedLength(c),
      d_prefixC(c),
      d_suffixC(c)
{
}

void EqcInfo::initializeConstant(Node c)
{
  for (size_t i=0; i<2; i++)
  {
    CExp& ce = i==0 ? d_suffixC : d_prefixC;
    ce.d_t = c;
    ce.d_c = c;
  }
}

Node EqcInfo::addEndpointConst(TNode t, TNode c, TNode exp, bool isSuf)
{
  Assert (!t.isNull());
  // check conflict
  CExp& cprev = isSuf ? d_suffixC : d_prefixC;
  TNode prevT = cprev.d_t.get();
  if (!prevT.isNull())
  {
    Trace("strings-eager-pconf-debug") << "Check conflict " << prevT << ", " << t
                                       << " post=" << isSuf << std::endl;
    TNode prevC = cprev.d_c.get();
    Assert(!prevC.isNull());
    Assert(prevC.isConst());
    Assert(!c.isNull());
    Assert(c.isConst());
    bool conflict = false;
    // if the constant prefixes are different
    if (c != prevC)
    {
      // conflicts between constants should be handled by equality engine
      Assert(!t.isConst() || !prevT.isConst());
      Trace("strings-eager-pconf-debug")
          << "Check conflict constants " << prevC << ", " << c << std::endl;
      size_t pvs = Word::getLength(prevC);
      size_t cvs = Word::getLength(c);
      if (pvs == cvs || (pvs > cvs && t.isConst())
          || (cvs > pvs && prevT.isConst()))
      {
        // If equal length, cannot be equal due to node check above.
        // If one is fully constant and has less length than the other, then the
        // other will not fit and we are in conflict.
        conflict = true;
      }
      else
      {
        TNode larges = pvs > cvs ? prevC : c;
        TNode smalls = pvs > cvs ? c : prevC;
        if (isSuf)
        {
          conflict = !Word::hasSuffix(larges, smalls);
        }
        else
        {
          conflict = !Word::hasPrefix(larges, smalls);
        }
      }
      if (!conflict && (pvs > cvs || prevT.isConst()))
      {
        // current is subsumed, either shorter prefix or the other is a full
        // constant
        return Node::null();
      }
    }
    else if (!t.isConst())
    {
      // current is subsumed since the other may be a full constant
      return Node::null();
    }
    if (conflict)
    {
      Trace("strings-eager-pconf")
          << "Conflict for " << prevC << ", " << c << std::endl;
      std::vector<Node> confExp;
      if (!exp.isNull())
      {
        confExp.push_back(exp);
      }
      if (!cprev.d_exp.get().isNull())
      {
        confExp.push_back(cprev.d_exp.get());
      }
      if (t != prevT)
      {
        confExp.push_back(t.eqNode(prevT));
      }
      Assert(!confExp.empty());
      // exp ^ prev.exp ^ t = prev.t
      Node ret = NodeManager::currentNM()->mkAnd(confExp);
      Trace("strings-eager-pconf")
          << "String: eager prefix conflict: " << ret << std::endl;
      return ret;
    }
  }
  // store
  cprev.d_t = t;
  cprev.d_c = c;
  cprev.d_exp = exp;
  return Node::null();
}

Node EqcInfo::addEndpointConst(CExp& ce, bool isSuf)
{
  if (ce.isNull())
  {
    return Node::null();
  }
  return addEndpointConst(ce.d_t.get(), ce.d_c.get(), ce.d_exp.get(), isSuf);
}

Node EqcInfo::checkEqualityConflict(TNode t, TNode c, TNode exp)
{
  Node prevT = d_prefixC.d_t;
  if (!prevT.isConst())
  {
    return Node::null();
  }
  Node eq = Rewriter::rewrite(prevT.eqNode(c));
  if (eq.isConst() && !eq.getConst<bool>())
  {
    // conflict
    std::vector<Node> confExp;
    
  }
  return Node::null();
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
