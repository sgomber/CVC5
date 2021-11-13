
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
class CongruenceClosureFv : protected EnvObj
{
public:
  CongruenceClosureFv(Env& env);
  void check();
private:
  /** are we finished? */
  bool isFinished() const;
  TNode getNextVariable();
  /** 
   * Push variable v to the stack.
   */
  void pushVar(TNode v);
  void popVar();
  
  void assignVar(TNode v, TNode eqc);


  bool eqNotifyTriggerPredicate(TNode predicate, bool value);
  bool eqNotifyTriggerTermEquality(TheoryId tag,
                                    TNode t1,
                                    TNode t2,
                                    bool value);

  void eqNotifyConstantTermMerge(TNode t1, TNode t2);
  void eqNotifyNewClass(TNode t);
  void eqNotifyMerge(TNode t1, TNode t2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);

  /**
  * Called when it is determined what pattern p is equal to.
  * 
  * If g is non-null, then g is the (ground) equivalence class that pattern p is
  * equal to.
  * If g is null, then we have determined that p will *never* merge into a
  * ground equivalence class in this context.
  */
  void notifyPatternEqGround(TNode p, TNode g);
  /**
   * Called when the current watched match term was 
   */
  void notifyQuantMatch(TNode q, bool success);

  /** the set of ground equivalence classes */
  NodeSet d_groundEqc;
  
  /** The current stack of quantified variables */
  std::vector<TNode> d_varStack;
  
  /** The set of quantified formulas */
  QuantifiersSet d_qset;
  
  /** Map quantified formulas to their info */
  std::map<Node, QuantInfo> d_quantInfo;
  /** Free variable info */
  std::map<Node, FreeVarInfo > d_fvInfo;
  /** Pattern term info */
  std::map<Node, PatTermInto > d_pInfo;
  /** Equivalence class info */
  std::map<Node, EqcInfo > d_eqcInfo;
};


}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif

