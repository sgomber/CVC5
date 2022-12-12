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

#include "options/strings_options.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

std::string ModelEqcInfo::toString() const
{
  std::stringstream ss;
  ss << d_mnf << " / " << d_length;
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
  // get the maximum model length
  d_maxModelLen = options().strings.stringsModelMaxLength;
  if (d_maxModelLen < 65536)
  {
    d_maxModelLen = 65536;
  }
}

bool StringsMnf::findModelNormalForms(const std::vector<Node>& stringsEqc)
{
  Trace("strings-mnf") << "StringsMnf::findModelNormalForms..." << std::endl;
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
  Trace("strings-mnf") << "...return: " << ret << std::endl;
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
    Trace("strings-mnf") << "NF " << eqc << " (empty): " << mei.toString()
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
    ++eqc_i;
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
      Trace("strings-mnf") << "Fail: " << eqc << " has no length term."
                           << std::endl;
      return false;
    }
    // otherwise, look up the model value now
    Valuation& val = d_state.getValuation();
    mei.d_length = val.getModelValue(lt).getConst<Rational>();
    mei.d_mnf.emplace_back(eqc);
    Trace("strings-mnf") << "NF " << eqc << " (singular): " << mei.toString()
                         << std::endl;
    return true;
  }

  // now, process each normal form
  bool firstTime = true;
  // list of modifications done to normal forms while processing this
  // equivalence class
  std::vector<std::pair<Node, std::vector<Node>>> currExpands;
  for (std::pair<Node, std::vector<Node>>& nf : nfs)
  {
    if (firstTime)
    {
      // first one sets the model normal form of the overall eqc
      mei.d_mnf = nf.second;
      firstTime = false;
      continue;
    }
    // First, update nf.second based on expands done for previous normal forms
    // in this equivalence class
    for (const std::pair<Node, std::vector<Node>>& ce : currExpands)
    {
      ModelEqcInfo::expandNormalForm(nf.second, ce.first, ce.second);
    }
    Trace("strings-mnf-solve") << "Compare: " << std::endl;
    Trace("strings-mnf-solve") << "[1] " << mei.d_mnf << std::endl;
    Trace("strings-mnf-solve") << "[2] " << nf.second << std::endl;

    // Now, compare mei.d_mnf and nf.second left to right
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
      Rational la = getLength(a);
      Rational lb = getLength(b);
      Trace("strings-mnf-solve")
          << "Compare " << a << " / " << b << ", lengths=" << la << " / " << lb
          << std::endl;
      // should have positive lengths
      Assert(la.sgn() == 1 && lb.sgn() == 1);
      // if lengths are already equal, merge b into a
      if (la == lb)
      {
        // flip if b is constant but a is not
        if (b.isConst())
        {
          if (a.isConst())
          {
            // conflict, we fail
            Trace("strings-mnf") << "Fail: " << eqc << " while merging " << a
                                << ", " << b << std::endl;
            return false;
          }
          else
          {
            std::swap(a,b);
          }
        }
        // otherwise merge b into a
        merge(a, b);
        // remember the operation
        currExpands.emplace_back(b, std::vector<Node>{a});
        i++;
      }
      else if (la > lb)
      {
        // otherwise, split
        std::vector<Node> avec = split(a, la, lb);
        currExpands.emplace_back(a, avec);
      }
      else
      {
        Assert(la < lb);
        std::vector<Node> bvec = split(b, lb, la);
        currExpands.emplace_back(b, bvec);
      }
      // apply the expansion to the current normal form (nf.second) we are
      // processing
      Assert(!currExpands.empty());
      std::pair<Node, std::vector<Node>> ce = currExpands.back();
      ModelEqcInfo::expandNormalForm(nf.second, ce.first, ce.second);
    }
  }
  // otherwise don't need to compute the length from the normal form
  Trace("strings-mnf") << "NF " << eqc << " : " << mei.toString() << std::endl;
  return true;
}

Rational StringsMnf::getLength(const Node& r)
{
  Assert(r.getType().isStringLike());
  if (r.isConst())
  {
    return Word::getLength(r);
  }
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

void StringsMnf::merge(const Node& a, const Node& b)
{
  // should not merge constant
  Assert (!b.isConst());
  Assert(a == getModelRepresentative(a));
  Assert(b == getModelRepresentative(b));
  Trace("strings-mnf") << "...merge " << b << ": " << a << std::endl;
  d_mrepMap[b] = a;
  // don't need the normal form info for b anymore?
  d_minfo.erase(b);
  // replace b with a in all current normal forms
  std::vector<Node> vec{a};
  expandNormalForms(b, vec);
}

std::vector<Node> StringsMnf::split(const Node& a,
                                    const Rational& alen,
                                    const Rational& pos)
{
  Assert(alen > pos);
  Assert(pos.sgn() == 1);
  std::vector<Node> vec;
  if (a.isConst())
  {
    // split concretely
    // since pos is less than alen which is the length of the constant, which
    // should be less than the maximum model length (or 65536).
    Assert(pos < d_maxModelLen);
    Assert(alen < d_maxModelLen);
    std::size_t pvalue = pos.getNumerator().toUnsignedInt();
    std::size_t alvalue = alen.getNumerator().toUnsignedInt();
    vec.push_back(Word::prefix(a, pvalue));
    vec.push_back(Word::suffix(a, alvalue-pvalue));
  }
  else
  {
    // split based on skolems, these are dummy since there is no need to cache
    // them
    TypeNode atn = a.getType();
    SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
    vec.push_back(sm->mkDummySkolem("m", atn));
    vec.push_back(sm->mkDummySkolem("m", atn));
  }
  // Allocate new equivalence class infos. Note that in rare cases we may
  // split a word into components where one of those components is already
  // a representative. In this case, we don't 
  Assert(vec.size() == 2);
  std::map<Node, ModelEqcInfo>::iterator it;
  Trace("strings-mnf") << "...split " << a << ": " << vec << std::endl;
  for (size_t i = 0; i < 2; i++)
  {
    it = d_minfo.find(vec[i]);
    if (it == d_minfo.end())
    {
      // allocate, where the length depends on alen / pos
      ModelEqcInfo& meic = d_minfo[vec[i]];
      meic.d_mnf.push_back(vec[i]);
      meic.d_length = i == 0 ? pos : alen - pos;
      Trace("strings-mnf") << "NF " << vec[i] << " (split " << a
                           << "): " << meic.toString() << std::endl;
    }
  }
  // expand a in all current normal forms
  expandNormalForms(a, vec);
  return vec;
}

void StringsMnf::expandNormalForms(const Node& n, const std::vector<Node>& nn)
{
  // TODO: could do uselists
  for (std::pair<const Node, ModelEqcInfo>& m : d_minfo)
  {
    m.second.expand(n, nn);
  }
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
