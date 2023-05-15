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

#include "main/lemma_loader.h"

namespace cvc5 {
namespace main {

LemmaLoader::LemmaLoader(std::string& filename, parser::SymbolManager* sm) : d_filename(filename), d_symman(sm)
{
  
}
LemmaLoader::~LemmaLoader()
{
  
}
std::vector<Term> LemmaLoader::check()
{
  std::vector<Term> lemmas;
  // TODO
  return lemmas;
}
std::string LemmaLoader::getName()
{
  return "LemmaLoader";
}
std::string LemmaLoader::getFileName() { return d_filename; }


}  // namespace main
}  // namespace cvc5

