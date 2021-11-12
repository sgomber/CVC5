

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
  
private:
    
  void decideVar(TNode v);
  void assignVar(TNode v, TNode eqc);

  bool eqNotifyTriggerPredicate(TNode predicate, bool value);
  bool eqNotifyTriggerTermEquality(TheoryId tag,
                                    TNode t1,
                                    TNode t2,
                                    bool value);

  void eqNotifyConstantTermMerge(TNode t1, TNode t2);
  void eqNotifyNewClass(TNode t);
  void eqNotifyMerge(TNode t1, TNode t2);

  /**
  * Called when it is determined what pattern p is equal to.
  * 
  * If g is non-null, then g is the (ground) equivalence class that pattern p is
  * equal to.
  * If g is null, then we have determined that p will *never* merge into a
  * ground equivalence class in this context.
  */
  void notifyPatternEqGround(TNode p, TNode g);

  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
  /** the list of quantified formulas */
  std::vector<TNode> d_quants;
  /** The index of the quantified formula we are assigning the variables of */
  size_t d_qindex;
  
  /** The current stack of quantified variables */
  
  
};

