

class QuantInfo
{
public:
  //------------------- static
  /** 
   * List of canonical variables corresponding to each bound variable.
   */
  std::vector<TNode> d_canonVars;
  //-------------------
  /** is alive, false if we know it is not possible to construct a propagating instance for this quantified formula  */
  context::CDO<bool> d_isActive;
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
  /**
   * is active, false if it has merged to a ground equivalence class, or if
   * its variables have been fully assigned.
   */
  context::CDO<bool> d_isActive;
  /** the ground term we are equal to? */
  
  /** The number of unassigned variables */
  context::CDO<size_t> d_numUnassignVar;
  
  /** Add equality constraint */
  void addEqConstraint(TNode eqc, TNode parent)
  {
    
  }
  /** Add disequality constraint */
  void addDeqConstraint(TNode eqc, TNode parent)
  {
    
  }
  /** get constraints */
  const std::map<TNode, std::vector<TNode> >& getConstraints(bool isEq) const
  {
    return isEq ? d_gEqReq : d_gDeqReq;
  }
private:
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

