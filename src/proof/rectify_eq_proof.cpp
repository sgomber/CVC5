/*********************                                                        */
/*! \file rectify_eq_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "proof/rectify_eq_proof.h"

#include "proof/theory_proof.h"
#include "proof/simplify_boolean_node.h"

namespace CVC4 {

int RectifiableEqProof::rectify(
    theory::TheoryId theoryId,
    const theory::eq::EqProof& pf,
    std::shared_ptr<theory::eq::EqProof> subTrans,
    theory::eq::EqProof::PrettyPrinter* pPrettyPrinter)
{
  int neg = -1;
  Assert(theoryId == theory::THEORY_UF || theoryId == theory::THEORY_ARRAYS);
  bool ufProof = (theoryId == theory::THEORY_UF);
  std::string theoryName = theory::getStatsPrefix(theoryId);
  pf.debug_print(("pf::" + theoryName).c_str(), 0, pPrettyPrinter);
  Debug("pf::" + theoryName) << std::endl;

  Assert(pf.d_id == theory::eq::MERGED_THROUGH_TRANS);
  Assert(!pf.d_node.isNull());
  Assert(pf.d_children.size() >= 2);

  subTrans->d_id = theory::eq::MERGED_THROUGH_TRANS;
  subTrans->d_node = pf.d_node;

  size_t i = 0;
  while (i < pf.d_children.size())
  {
    // special treatment for uf and not for array
    if (ufProof
        || pf.d_children[i]->d_id != theory::eq::MERGED_THROUGH_CONGRUENCE)
    {
      pf.d_children[i]->d_node = simplifyBooleanNode(pf.d_children[i]->d_node);
    }

    // Look for the negative clause, with which we will form a contradiction.
    if (!pf.d_children[i]->d_node.isNull()
        && pf.d_children[i]->d_node.getKind() == kind::NOT)
    {
      Assert(neg < 0);
      (neg) = i;
      ++i;
    }

    // Handle congruence closures over equalities.
    else if (pf.d_children[i]->d_id == theory::eq::MERGED_THROUGH_CONGRUENCE
             && pf.d_children[i]->d_node.isNull())
    {
      Debug("pf::" + theoryName) << "Handling congruence over equalities"
                                 << std::endl;

      // Gather the sequence of consecutive congruence closures.
      std::vector<std::shared_ptr<const theory::eq::EqProof>>
          congruenceClosures;
      unsigned count;
      Debug("pf::" + theoryName) << "Collecting congruence sequence"
                                 << std::endl;
      for (count = 0; i + count < pf.d_children.size()
                      && pf.d_children[i + count]->d_id
                             == theory::eq::MERGED_THROUGH_CONGRUENCE
                      && pf.d_children[i + count]->d_node.isNull();
           ++count)
      {
        Debug("pf::" + theoryName) << "Found a congruence: " << std::endl;
        pf.d_children[i + count]->debug_print(
            ("pf::" + theoryName).c_str(), 0, pPrettyPrinter);
        congruenceClosures.push_back(pf.d_children[i + count]);
      }

      Debug("pf::" + theoryName)
          << "Total number of congruences found: " << congruenceClosures.size()
          << std::endl;

      // Determine if the "target" of the congruence sequence appears right
      // before or right after the sequence.
      bool targetAppearsBefore = true;
      bool targetAppearsAfter = true;

      if ((i == 0) || (i == 1 && neg == 0))
      {
        Debug("pf::" + theoryName) << "Target does not appear before"
                                   << std::endl;
        targetAppearsBefore = false;
      }

      if ((i + count >= pf.d_children.size())
          || (!pf.d_children[i + count]->d_node.isNull()
              && pf.d_children[i + count]->d_node.getKind() == kind::NOT))
      {
        Debug("pf::" + theoryName) << "Target does not appear after"
                                   << std::endl;
        targetAppearsAfter = false;
      }

      // Flow changes between uf and array
      if (ufProof)
      {
        // Assert that we have precisely at least one possible clause.
        Assert(targetAppearsBefore || targetAppearsAfter);

        // If both are valid, assume the one after the sequence is correct
        if (targetAppearsAfter && targetAppearsBefore)
        {
          targetAppearsBefore = false;
        }
      }
      else
      {  // not a uf proof
        // Assert that we have precisely one target clause.
        Assert(targetAppearsBefore != targetAppearsAfter);
      }

      // Begin breaking up the congruences and ordering the equalities
      // correctly.
      std::vector<std::shared_ptr<theory::eq::EqProof>> orderedEqualities;

      // Insert target clause first.
      if (targetAppearsBefore)
      {
        orderedEqualities.push_back(pf.d_children[i - 1]);
        // The target has already been added to subTrans; remove it.
        subTrans->d_children.pop_back();
      }
      else
      {
        orderedEqualities.push_back(pf.d_children[i + count]);
      }

      // Start with the congruence closure closest to the target clause, and
      // work our way back/forward.
      if (targetAppearsBefore)
      {
        for (unsigned j = 0; j < count; ++j)
        {
          if (pf.d_children[i + j]->d_children[0]->d_id
              != theory::eq::MERGED_THROUGH_REFLEXIVITY)
            orderedEqualities.insert(orderedEqualities.begin(),
                                     pf.d_children[i + j]->d_children[0]);
          if (pf.d_children[i + j]->d_children[1]->d_id
              != theory::eq::MERGED_THROUGH_REFLEXIVITY)
            orderedEqualities.insert(orderedEqualities.end(),
                                     pf.d_children[i + j]->d_children[1]);
        }
      }
      else
      {
        for (unsigned j = 0; j < count; ++j)
        {
          if (pf.d_children[i + count - 1 - j]->d_children[0]->d_id
              != theory::eq::MERGED_THROUGH_REFLEXIVITY)
            orderedEqualities.insert(
                orderedEqualities.begin(),
                pf.d_children[i + count - 1 - j]->d_children[0]);
          if (pf.d_children[i + count - 1 - j]->d_children[1]->d_id
              != theory::eq::MERGED_THROUGH_REFLEXIVITY)
            orderedEqualities.insert(
                orderedEqualities.end(),
                pf.d_children[i + count - 1 - j]->d_children[1]);
        }
      }

      // Copy the result into the main transitivity proof.
      subTrans->d_children.insert(subTrans->d_children.end(),
                                  orderedEqualities.begin(),
                                  orderedEqualities.end());

      // Increase i to skip over the children that have been processed.
      i += count;
      if (targetAppearsAfter)
      {
        ++i;
      }
    }

    // Else, just copy the child proof as is
    else
    {
      subTrans->d_children.push_back(pf.d_children[i]);
      ++i;
    }
  }

  bool disequalityFound = (neg >= 0);
  if (!disequalityFound)
  {
    Debug("pf::" + theoryName)
        << "A disequality was NOT found. UNSAT due to merged constants"
        << std::endl;
    Debug("pf::" + theoryName) << "Proof for: " << pf.d_node << std::endl;
    Assert(pf.d_node.getKind() == kind::EQUAL);
    Assert(pf.d_node.getNumChildren() == 2);
    Assert(pf.d_node[0].isConst() && pf.d_node[1].isConst());
  }
  return neg;
}  
  
void RectifiableEqProof::rectify(theory::TheoryId theoryId)
{
  if( !d_subTrans )
  {
    d_subTrans =
        std::make_shared<theory::eq::EqProof>();
    d_negStatus = rectify(theoryId, *d_proof, d_subTrans);
  }
}

} /* namespace CVC4 */
