/******************************************************************************
 * Top contributors (to current version):
 *   Daniel Kroening, Elizabeth Polgreen
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Creates and deletes tmp files. Won't work for windows
 */

#ifndef CVC5__UTIL__TMPFILE_H
#define CVC5__UTIL__TMPFILE_H

#include <string>

namespace cvc5 {

// Returns an unused file name for a writeable temporary file,
// and makes sure it exists.
std::string get_temporary_file(const std::string& prefix,
                               const std::string& suffix);

// The below deletes the temporary file upon destruction,
// cleaning up after you in case of exceptions.
class temporary_filet
{
 public:
  temporary_filet(const std::string& prefix, const std::string& suffix)
      : name(get_temporary_file(prefix, suffix))
  {
  }

  // Using the copy constructor would delete the file twice.
  temporary_filet(const temporary_filet&) = delete;

  temporary_filet(temporary_filet&& other) { name.swap(other.name); }

  // get the name
  std::string operator()() const { return name; }

  // will delete the file
  ~temporary_filet();

 protected:
  std::string name;
};

}  // namespace cvc5
#endif  // CVC5__UTIL__TMPFILE_H