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

#include <cvc5.h>

namespace cvc5 {
  
namespace parser{
class SymbolManager;  
}

namespace main {

class LemmaLoader : public cvc5::Plugin
{
 public:
  LemmaLoader(std::string& filename, parser::SymbolManager* sm);
  ~LemmaLoader();
  std::vector<Term> check() override;
  std::string getName() override;
  std::string getFileName();
 private:
  /** The symbol manager */
  parser::SymbolManager* d_symman;
  /** The filename to read from */
  std::string d_filename;
};

}  // namespace main
}  // namespace cvc5

#endif /* CVC5__LEMMA_LOADER_H */
