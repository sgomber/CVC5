/*********************                                                        */
/*! \file ee_manager_distributed.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for equality sharing.
 **/


#include "theory/ee_manager_distributed.h"

#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

EqEngineManagerDistributed::EqEngineManagerDistributed(TheoryEngine& te) : d_te(te)
{
}

EqEngineManagerDistributed::~EqEngineManagerDistributed()
{
}

void EqEngineManagerDistributed::finishInit()
{
  // allocate equality engines per theory
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST; ++ theoryId) {
    Theory * t = d_te.theoryOf(theoryId);
    if (t == nullptr) 
    {
      // theory not active, skip
      continue;
    }
    // allocate an equality engine
    EeTheoryInfo& eet = d_einfo[theoryId];
    eet.d_allocEe.reset(t->allocateEqualityEngine());
  }
  
  const LogicInfo& logicInfo = d_te.getLogicInfo();
  if (logicInfo.isQuantified())
  {
    // construct the master equality engine
    Assert(d_masterEqualityEngine == nullptr);
    d_masterEqualityEngine.reset(new eq::EqualityEngine(d_te.getSatContext(), "theory::master", false));

    for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST; ++ theoryId) {
      Theory * t = d_te.theoryOf(theoryId);
      if (t == nullptr) 
      {
        // theory not active, skip
        continue;
      }
      EeTheoryInfo& eet = d_einfo[theoryId];
      // get the allocated equality engine
      eq::EqualityEngine * eeAlloc = eet.d_allocEe.get();
      if (eeAlloc!=nullptr)
      {
        // set the master equality engine of the theory's equality engine
        eeAlloc->setMasterEqualityEngine(d_masterEqualityEngine.get());
      }
    }
  }
}
eq::EqualityEngine* EqEngineManagerDistributed::getMasterEqualityEngine()
{
  return d_masterEqualityEngine.get();
}

}  // namespace theory
}  // namespace CVC4

