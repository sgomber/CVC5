
class SmtSolverDriver
{
public:
  SmtSolverDriver(SmtSolver * smt) : d_smt(smt){}
  virtual void notifyInputFormulas(std::vector<Node> ppAssertions, std::unordered_map<size_t, Node> ppSkolemMap) = 0;
  virtual void finishCheckSat() = 0;
  enum class CheckAgainStatus
  {
    PREPROCESS_SOLVE_AGAIN,
    SOLVE_AGAIN,
    FINISH
  };
  /**
   * Return true if we should check again. If so, we populate assertions
   * with the set of things that should be preprocessed
   */
  virtual CheckAgainStatus checkAgain(Assertions& as) = 0;
private:
  /** The underlying SMT solver */
  SmtSolver * d_smt;
};

class SmtSolverDriverSingleCall : public SmtSolverDriver
{
public:
  SmtSolverDriverSingleCall(SmtSolver * smt) : SmtSolverDriver(smt){}
  
  void notifyInputFormulas(std::vector<Node> ppAssertions, std::unordered_map<size_t, Node> ppSkolemMap) override
  {
    // immediately assert all formulas to the underlying prop engine
    d_smt->getPropEngine()->assertInputFormulas(ppAssertions, ppSkolemMap);
  }
  void finishCheckSat() override
  {
    // do nothing
  }
  CheckAgainStatus checkAgain(Assertions& as) override
  {
    return CheckAgainStatus::FINISH;
  }
};
