

class QuantInfo
{
public:
  //------------------- static
  /** 
   * List of canonical variables corresponding to each bound variable.
   */
  std::vector<TNode> d_canonVars;
  //-------------------
};

class FreeVarInfo
{
public:
  /** term list, all pattern terms that contain this variable */
  std::vector<TNode> d_useList;
};

/**
 * A quantified formula is a pattern term whose parent is
 * the quant
 */
class PatTermInto
{
public:
  /** is alive, false if we know it is not possible to construct a propagating instance with this term  */
  context::CDO<bool> d_isActive;
  /** the ground term we are equal to? */
  
  /** The number of unassigned variables */
  context::CDO<size_t> d_numUnassignVar;
  /**
   * Map from equivalence classes to pattern terms that require
   * this pattern to be in the equivalence class of that term. If the pattern term
   * merges into a equivalence class that is not that equivalence class,
   * the quantified formula has no propagating substitution in the context, and hence it is marked dead.
  */
  std::map<TNode, std::vector<TNode> > d_gEqReq;
  /** Same as above, for disequality requirements */
  std::map<TNode, std::vector<TNode> > d_gDeqReq; 
  /**
   * The list of pattern terms that are the parent of this. For pattern p,
   * this is either:
   * (1) A term of the form f( ... p ... )
   * (2) A quantified formula Q that is a Boolean connective with p as an atom.
   */
  //std::vector<TNode> d_parents;
};

/** For each equivalence class
 * 
 * P(x, y) P(x, z)
 * y = a, z = a
 * P(x, a), P(x, b), a = b
 */
class EqcInfo
{
  typedef context::CDList<Node> NodeList;
public:
  /** List of terms in this equivalence class that are not the representative */
  NodeList d_eqPats;
};



class EqEngineState
{
  typedef context::CDHashSet<Node> NodeSet;
public:
  /** the set of ground equivalence classes */
  NodeSet d_groundEqc;
  /** total number of alive quantified formulas */
  context::CDO<size_t> d_numAlive;
};





bool eqNotifyTriggerPredicate(TNode predicate, bool value)
{

}

bool eqNotifyTriggerTermEquality(TheoryId tag,
                                  TNode t1,
                                  TNode t2,
                                  bool value)
{

}

void eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  // should never happen
  Assert(false);
}

void eqNotifyNewClass(TNode t)
{
  // do nothing
}

void eqNotifyMerge(TNode t1, TNode t2)
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

/**
 * Called when it is determined what pattern p is equal to.
 * 
 * If g is non-null, then g is the (ground) equivalence class that pattern p is
 * equal to.
 * If g is null, then we have determined that p will *never* merge into a
 * ground equivalence class in this context.
 */
void notifyPatternEqGround(TNode p, TNode g)
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

void eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{

}



/**

Q1: x : T1, y : T2
Q2: y : T2, w : T2

--- Q1
x -> a
  --- Q2
  y -> b
    w -> c
    w -> d
  y -> c
    w -> d
  y -> d
  y -> e
x -> b
  y -> b
  y -> e
  y -> f

*/

class CongruenceClosureFv
{
public:
  /** the list of quantified formulas */
  std::vector<TNode> d_quants;
  /** The index of the quantified formula we are assigning the variables of */
  size_t d_qindex;
  
  /** The current stack of quantified variables */
};

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
