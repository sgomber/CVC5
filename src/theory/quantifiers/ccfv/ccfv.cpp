


bool CongruenceClosureFv::eqNotifyTriggerPredicate(TNode predicate, bool value)
{

}

bool CongruenceClosureFv::eqNotifyTriggerTermEquality(TheoryId tag,
                                  TNode t1,
                                  TNode t2,
                                  bool value)
{

}

void CongruenceClosureFv::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  // should never happen
  Assert(false);
}

void CongruenceClosureFv::eqNotifyNewClass(TNode t)
{
  // do nothing
}

void CongruenceClosureFv::eqNotifyMerge(TNode t1, TNode t2)
{
  if (d_groundEqc.find(t1)!=d_groundEqc.end())
  {
    // should never merge ground equivalence classes
    Assert (d_groundEqc.find(t2)==d_groundEqc.end());
    // swap
    std::swap(t1, t2);
  }
  else if (d_groundEqc.find(t2)!=d_groundEqc.end())
  {
    // update the list of ground equivalence classes, which is overapproximated
    // i.e. we do not remove t2
    d_state.d_groundEqc.insert(t1);
  }
  else
  {
    // two patterns merging, track the list
    EqcInfo * eq2 = getOrMkEqcInfo(t2);
    EqcInfo * eq1 = getOrMkEqcInfo(t1, true);
    eq1->d_eqPats.insert(t2);
    if (eq2!=nullptr)
    {
      eq1->d_eqPats.insert(eq2->d_eqPats.begin(), eq2->d_eqPats.end());
    }
    return;
  }
  // we are in a situation where a ground equivalence class t2 has merged
  // with a pattern equivalence class.
  // notify the pattern for the representative
  notifyPatternEqGround(t1, t2);
  // if there are patterns equal to this one, notify them too
  EqcInfo * eq = getOrMkEqcInfo(t1);
  if (eq!=nullptr)
  {
    for (TNode t : d_state.d_eqPats)
    {
      notifyPatternEqGround(t, t2);
    }
  }
}

void CongruenceClosureFv::notifyPatternEqGround(TNode p, TNode g)
{
  const PatTermInto& pti = getPatternTermInfo(p);
  // if still active
  if (!pti.d_isActive)
  {
    return;
  }
  pti.d_isActive = false;
  for (size_t i=0; i<2; i++)
  {
    const std::map<const TNode, std::vector<TNode> >& req = i==0 ? pti.d_gEqReq : pti.d_gDeqReq;
    bool processEq = (i==0);
    for (const std::pair<const TNode, std::vector<TNode> >& r : req)
    {
      Assert (r.first.isNull() || d_equalityEngine.hasTerm(r.first));
      if (!g.isNull())
      {
        if (!r.first.isNull() || (d_equalityEngine.getRepresentative(r.first)==g) == processEq)
        {
          // the required constraint was satisfied, do not mark dead
          continue;
        }
      }
      // mark all as dead
      for (TNode n : r.second)
      {
        // parent could be a quantified formula
        if (n.getKind()==FORALL)
        {
          // notify
        }
        else
        {
          eqNotifyPatternEqGround(n, Node::null());
        }
      }
    }
  }
}

void CongruenceClosureFv::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{

}

void CongruenceClosureFv::decideVar(TNode v)
{
  // compute the equivalence classes we should assign
  std::vector<TNode> eqcToAssign;
  
  // decrement the # assigned variables in each term that contains it, which
  // also computes which terms are newly fully assigned
  std::vector<TNode> fullAssignedPats;
  
  //
  for (TNode g : eqcToAssign)
  {
    assignVar(v, q);
    // for each fully assigned pattern, mark dead
    for (TNode p : fullAssignedPats)
    {
      notifyPatternEqGround(p, d_null);
    }
    
  }
}

void CongruenceClosureFv::assignVar(TNode v, TNode eqc)
{
  Node eq = v.eqNode(eqc);
  d_ee->assertEquality(eq);
}
