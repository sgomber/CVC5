/*********************                                                        */
/*! \file decision_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of Decision manager, which manages all decision
 ** strategies owned by theory solvers within TheoryEngine.
 **/

#include "theory/decision_manager.h"

#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

DecisionManager::DecisionManager(context::Context * userContext) : d_strategyCache(userContext){}

void DecisionManager::presolve()
{
  Trace("dec-manager") << "DecisionManager: presolve." << std::endl;
  //d_reg_strategy.clear();
  // remove the strategies that are not in this user context
  std::unordered_set<DecisionStrategy*> strats;
  for( DecisionStrategyList::const_iterator i = d_strategyCache.begin(); i != d_strategyCache.end(); ++i ) {
    strats.insert( *i );
  }
  for (std::pair<const StrategyId, std::vector<DecisionStrategy*> >& rs :
       d_reg_strategy)
  {
    unsigned i=0;
    while (strats.find(rs.second[i])!=strats.end())
    {
      i++;
    }
    if (i<rs.second.size())
    {
      Trace("dec-manager") << "DecisionManager: remove " << rs.second.size()-i << "/" << rs.second.size() << " strategies for id " << rs.first << std::endl;
      rs.second.erase( rs.second.begin()+i, rs.second.end());
    }
  }
}

void DecisionManager::registerStrategy(StrategyId id, DecisionStrategy* ds)
{
  Trace("dec-manager") << "DecisionManager: Register strategy : "
                       << ds->identify() << ", id = " << id << std::endl;
  ds->initialize();
  d_reg_strategy[id].push_back(ds);
  // store it in the user-context-dependent list
  d_strategyCache.push_back(ds);
}

Node DecisionManager::getNextDecisionRequest()
{
  Trace("dec-manager-debug")
      << "DecisionManager: Get next decision..." << std::endl;
  for (const std::pair<const StrategyId, std::vector<DecisionStrategy*> >& rs :
       d_reg_strategy)
  {
    for (unsigned i = 0, size = rs.second.size(); i < size; i++)
    {
      DecisionStrategy* ds = rs.second[i];
      Node lit = ds->getNextDecisionRequest();
      if (!lit.isNull())
      {
        Trace("dec-manager")
            << "DecisionManager:  -> literal " << lit << " decided by strategy "
            << ds->identify() << std::endl;
        return lit;
      }
      Trace("dec-manager-debug") << "DecisionManager:  " << ds->identify()
                                 << " has no decisions." << std::endl;
    }
  }
  Trace("dec-manager-debug")
      << "DecisionManager:  -> no decisions." << std::endl;
  return Node::null();
}

}  // namespace theory
}  // namespace CVC4
