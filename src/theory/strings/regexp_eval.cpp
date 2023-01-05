/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Evaluator for regular expression membership.
 */

#include "theory/strings/regexp_eval.h"

#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

class NfaState
{
public:
  /** maps single character RE to children */
  std::map<Node, NfaState*> d_children;
  
  static NfaState* construct(Node r, NfaState* accept, std::vector<std::shared_ptr<NfaState>>& scache)
  {
    NfaState * rs = constructInternal(r, scache);
    rs->connectTo(accept);
    return rs;
  }
    
  static NfaState* constructInternal(Node r, std::vector<std::shared_ptr<NfaState>>& scache)
  {
    Kind k = r.getKind();
    if (k==REGEXP_CONCAT)
    {
      NfaState * first = nullptr;
      NfaState * curr = nullptr;
      for (const Node& rc : r)
      {
        NfaState * rcs = constructInternal(rc, scache);
        if (first==nullptr)
        {
          first = rcs;
          curr = first;
          continue;
        }
        // connect previous to next
        curr->connectTo(rcs);
        // update current
        curr = rcs;
      }
      // should have had 2+ arguments
      Assert (curr!=first && curr!=nullptr && first!=nullptr);
      // copy arrows from last to first
      first->d_arrows = curr->d_arrows;
      curr->d_arrows.clear();
      return first;
    }
    // otherwise allocate a state
    NfaState* s = allocateState(scache);
    std::vector<std::pair<NfaState*, Node>>& sarrows = s->d_arrows;
    switch(k)
    {
      case STRING_TO_REGEXP:
      {
        Assert (r[0].isConst());
        const String& str = r[0].getConst<String>();
        if (str.size()==0)
        {
          // NOTE: does this ever happen in this fragment?
          sarrows.emplace_back(s, Node::null());
        }
        else
        {
          const std::vector<unsigned>& vec = str.getVec();
          NfaState * curr = s;
          NodeManager * nm = NodeManager::currentNM();
          for (size_t i=0, nvec = vec.size(); i<nvec; i++)
          {
            std::vector<unsigned> charVec{vec[i]};
            Node nextChar = nm->mkConst(String(charVec));
            if (i+1==vec.size())
            {
              sarrows.emplace_back(curr, nextChar);
            }
            else
            {
              NfaState * next = allocateState(scache);
              curr->d_children[nextChar] = next;
            }
          }
        }
      }
        break;
      case REGEXP_ALLCHAR:
      case REGEXP_RANGE:
        sarrows.emplace_back(s, r);
        break;
      case REGEXP_UNION:
      {
        // take union of arrows
        for (const Node& rc : r)
        {
          NfaState * rcs = constructInternal(rc, scache);
          std::vector<std::pair<NfaState*, Node>>& rcsarrows = rcs->d_arrows;
          sarrows.insert(sarrows.end(), rcsarrows.begin(), rcsarrows.end());
          rcsarrows.clear();
        }
      }
        break;
      case REGEXP_STAR:
      {
        NfaState * body = constructInternal(r[0], scache);
        // loops back to this state
        body->connectTo(s);
        // skip moves on
        sarrows.emplace_back(s, Node::null());
      }
        break;
      default:
        break;
    }
    return s;
  }
private:
  void connectTo(NfaState* s)
  {
    for(std::pair<NfaState*, Node>& a : d_arrows)
    {
      a.first->d_children[a.second] = s;
    }
    d_arrows.clear();
  }
  static NfaState * allocateState(std::vector<std::shared_ptr<NfaState>>& scache)
  {
    std::shared_ptr<NfaState> ret = std::make_shared<NfaState>();
    scache.push_back(ret);
    return ret.get();
  }
  /** Current dangling */
  std::vector<std::pair<NfaState*, Node>> d_arrows;
};

bool evalMembership(String& s, const Node& r)
{
  // TODO: assert no intersection, complement, or non-constant.

  return false;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
