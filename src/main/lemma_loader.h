/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Lemma loader for cvc5.
 */

#ifndef CVC5__LEMMA_LOADER_H
#define CVC5__LEMMA_LOADER_H

#include <cvc5/cvc5.h>

namespace cvc5 {
  
namespace parser{
class SymbolManager;  
}

namespace main {

class LemmaLoader : public cvc5::Plugin
{
 public:
  LemmaLoader(std::string& filename, Solver * s, parser::SymbolManager* sm);
  ~LemmaLoader();
  std::vector<Term> check() override;
  std::string getName() override;
  std::string getFileName();
 private:
  /** The filename to read from */
  std::string d_filename;
  /** The solver we are associated with */
  Solver * d_solver;
  /** The symbol manager (for parsing) */
  parser::SymbolManager* d_symman;
};

}  // namespace main
}  // namespace cvc5

#endif /* CVC5__LEMMA_LOADER_H */
