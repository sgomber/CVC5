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

namespace cvc5::internal {
namespace theory {
namespace strings {

class Position
{
public:
  Position() : d_isFinished(false) {}
  bool isFinished() const { return d_isFinished; }
  void update(unsigned nextChar, std::vector<Position>& pos);
private:
  bool d_isFinished;
  std::vector<size_t> d_index;
  Node getCurrent(const Node& r)
  {
    Node rr = r;
    for (size_t i, nindex = d_index.size(); i<nindex; i++)
    {
      Assert (d_index[i]<rr.getNumChildren());
      rr = rr[d_index[i]];
    }
    return rr;
  }
};

bool evalMembership(String& s, const Node& r)
{
  Assert (!expr::hasSubtermKind(r, REGEXP_INTERSECTION));
  std::vector<Position> pos;
  pos.push_back(Position());
  const std::vector<unsigned>& vec = s.getVec();
  for (unsigned nextChar : vec)
  {
    // only process those currently in position vector
    for (size_t j=0, npos = pos.size(); j<npos; j++)
    {
      pos[j].update(nextChar, pos);
    }
  }
  for (const Position& p : pos)
  {
    if (p.isFinished())
    {
      return true;
    }
  }
  return false;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
