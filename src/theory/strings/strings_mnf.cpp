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
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

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
  for (const Node& eqc : stringsEqc)
  {
    TypeNode stype = eqc.getType();
    if (!normalizeEqc(eqc, stype))
    {
      ret = false;
      break;
    }
  }
  // if successful and non-trivial, we will be the model constructor
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
  }
  return vec;
}

bool StringsMnf::normalizeEqc(Node eqc, TypeNode stype)
{
  ModelEqcInfo& mei = d_minfo[eqc];
  // if empty string, we initialize length to zero, normal form to empty
  Node emp = Word::mkEmptyWord(stype);
  if (d_state.areEqual(eqc, emp))
  {
    mei.d_length = d_zero;
    return true;
  }
  // otherwise, get the normal form for each term in the equivalence class
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
      // start with a list of representatives of children
      std::vector<Node> nrs;
      for (const Node& nc : n)
      {
        nrs.push_back(d_state.getRepresentative(nc));
      }
      // expand the list of representatives to normal form
      std::vector<Node> nf = expandNormalForm(nrs);
      // add to vector
      nfs.emplace_back(n, nf);
    }
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
    // compare mei.d_mnf and nf.second
  }
  return false;
}

std::vector<Node> StringsMnf::expandNormalForm(const std::vector<Node>& nf)
{
  std::vector<Node> exnf;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
