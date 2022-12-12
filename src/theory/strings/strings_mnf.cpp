/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model normal form finder for strings
 */

#include "theory/strings/strings_mnf.h"

#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

std::string ModelEqcInfo::toString() const
{
  std::stringstream ss;
  ss << d_mnf << "/" << d_length;
  return ss.str();
}

void ModelEqcInfo::expand(const Node& n, const std::vector<Node>& nn)
{
  expandNormalForm(d_mnf, n, nn);
}

void ModelEqcInfo::expandNormalForm(std::vector<Node>& mnf,
                                    const Node& n,
                                    const std::vector<Node>& nn)
{
  Assert(!nn.empty());
  size_t i = 0;
  while (i < mnf.size())
  {
    if (mnf[i] == n)
    {
      mnf[i] = nn[0];
      mnf.insert(mnf.begin() + i + 1, nn.begin() + 1, nn.end());
      i += nn.size();
    }
    else
    {
      i++;
    }
  }
}

StringsMnf::StringsMnf(Env& env,
                       SolverState& s,
                       InferenceManager& im,
                       TermRegistry& tr,
                       BaseSolver& bs)
    : ModelCons(env), d_state(s), d_im(im), d_termReg(tr), d_bsolver(bs)
{
  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));
}

bool StringsMnf::findModelNormalForms(const std::vector<Node>& stringsEqc)
{
  bool ret = true;
  // reset the state
  d_minfo.clear();
  d_mrepMap.clear();
  // try to find model normal form for each equivalence class, where stringsEqc
  // is sorted based on containment ordering
  for (const Node& eqc : stringsEqc)
  {
    TypeNode stype = eqc.getType();
    if (!normalizeEqc(eqc, stype))
    {
      ret = false;
      break;
    }
  }
  // if successful and non-trivial, this class will be the model constructor
  if (ret && !stringsEqc.empty())
  {
    d_state.setModelConstructor(this);
  }
  return ret;
}

void StringsMnf::getStringRepresentativesFrom(
    const std::set<Node>& termSet,
    std::unordered_set<TypeNode>& repTypes,
    std::map<TypeNode, std::unordered_set<Node>>& repSet)
{
  // TODO
}

void StringsMnf::separateByLength(
    const std::vector<Node>& n,
    std::map<TypeNode, std::vector<std::vector<Node>>>& cols,
    std::map<TypeNode, std::vector<Node>>& lts)
{
  // TODO
}

std::vector<Node> StringsMnf::getNormalForm(Node n)
{
  Node r = getModelRepresentative(n);
  return getNormalFormInternal(r);
}

std::vector<Node> StringsMnf::getNormalFormInternal(const Node& n)
{
  Assert(n == getModelRepresentative(n));
  std::vector<Node> vec;
  std::map<Node, ModelEqcInfo>::iterator it = d_minfo.find(n);
  if (it != d_minfo.end())
  {
    vec = it->second.d_mnf;
  }
  else
  {
    // Shouln't ask for normal forms of strings that weren't computed. This
    // likely means that n is not a representative or not a term in the current
    // context. We simply return a default normal form here in this case.
    Assert(false);
    vec.push_back(n);
  }
  return vec;
}

bool StringsMnf::normalizeEqc(Node eqc, TypeNode stype)
{
  ModelEqcInfo& mei = d_minfo[eqc];
  // if empty string, we initialize normal form to empty
  Node emp = Word::mkEmptyWord(stype);
  if (d_state.areEqual(eqc, emp))
  {
    mei.d_length = Rational(0);
    Trace("strings-mnf") << "NF " << eqc << " : (empty) " << mei.toString()
                         << std::endl;
    return true;
  }
  // NodeManager* nm = NodeManager::currentNM();
  //  otherwise, get the normal form for each term in the equivalence class
  std::vector<std::pair<Node, std::vector<Node>>> nfs;
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, ee);
  while (!eqc_i.isFinished())
  {
    Node n = (*eqc_i);
    if (d_bsolver.isCongruent(n))
    {
      continue;
    }
    if (utils::isConstantLike(n))
    {
      nfs.emplace_back(n, std::vector<Node>{n});
      continue;
    }
    if (n.getKind() == STRING_CONCAT)
    {
      // expand the normal form of the representative of each child
      std::vector<Node> nf;
      for (const Node& nc : n)
      {
        std::vector<Node> nfr = getNormalForm(nc);
        nf.insert(nf.end(), nfr.begin(), nfr.end());
      }
      // if not singular, add to vector
      if (nf.size() > 1 || (nf.size() == 1 && utils::isConstantLike(nf[0])))
      {
        nfs.emplace_back(n, nf);
      }
    }
  }

  // if we are an atomic equivalence class, just compute the length
  if (nfs.empty())
  {
    EqcInfo* ei = d_state.getOrMakeEqcInfo(eqc, false);
    Node lt = ei ? ei->d_lengthTerm : Node::null();
    if (lt.isNull())
    {
      // does not have a length term, we must fail
      return false;
    }
    // otherwise, look up the model value now
    Valuation& val = d_state.getValuation();
    mei.d_length = val.getModelValue(lt).getConst<Rational>();
    mei.d_mnf.emplace_back(eqc);
    Trace("strings-mnf") << "NF " << eqc << " : (singular) " << mei.toString()
                         << std::endl;
    return true;
  }

  // now, process each normal form
  bool firstTime = false;
  for (std::pair<Node, std::vector<Node>>& nf : nfs)
  {
    if (firstTime)
    {
      // first one sets the model normal form of the overall eqc
      mei.d_mnf = nf.second;
      firstTime = false;
      continue;
    }
    // compare mei.d_mnf and nf.second left to right
    size_t i = 0;
    while (i < mei.d_mnf.size())
    {
      Node a = mei.d_mnf[i];
      Node b = nf.second[i];
      if (a == b)
      {
        i++;
        continue;
      }
      const Rational& la = getLength(a);
      const Rational& lb = getLength(b);
      // if lengths are already equal, merge b into a
      if (la == lb)
      {
        if (!merge(a, b))
        {
          // conflict, we fail
          return false;
        }
      }
      // otherwise, split
      if (la > lb)
      {
      }
    }
  }

  Trace("strings-mnf") << "NF " << eqc << " : " << mei.toString() << std::endl;
  // compute the length from the normal form?
  return false;
}

const Rational& StringsMnf::getLength(const Node& r)
{
  std::map<Node, ModelEqcInfo>::iterator it = d_minfo.find(r);
  Assert(it != d_minfo.end());
  return it->second.d_length;
}

Node StringsMnf::getModelRepresentative(const Node& n)
{
  Node r = d_state.getRepresentative(n);
  std::map<Node, Node>::iterator it = d_mrepMap.find(r);
  if (it != d_mrepMap.end())
  {
    return it->second;
  }
  return r;
}

bool StringsMnf::merge(const Node& a, const Node& b)
{
  Assert(a == getModelRepresentative(a));
  Assert(b == getModelRepresentative(b));
  if (a.isConst() && b.isConst())
  {
    // cannot merge constants
    return false;
  }
  d_mrepMap[b] = a;
  // don't need the normal form info for b anymore?
  d_minfo.erase(b);
  return true;
}

std::vector<Node> StringsMnf::split(const Node& a, const Rational& pos)
{
  std::vector<Node> vec;
  if (a.isConst())
  {
    // split concretely
  }
  else
  {
    // split based on skolems
  }

  // expand a in all current normal forms
  for (std::pair<const Node, ModelEqcInfo>& m : d_minfo)
  {
    m.second.expand(a, vec);
  }
  return vec;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
