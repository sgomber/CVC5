/******************************************************************************
 * (C) 2001-2016, Daniel Kroening, Edmund Clarke,
 * Computer Science Department, University of Oxford
 * Computer Science Department, Carnegie Mellon University
 * 
 *  This file is adapted from CBMC utils https://github.com/diffblue/cbmc/util
 *
 * ****************************************************************************
 *
 *  Runs system commands. Won't work for windows
 */


#ifndef CVC5__RUN_H
#define CVC5__RUN_H

#include <iosfwd>
#include <string>
#include <vector>



namespace cvc5 {
/// This performs shell quoting if necessary on input \p src.
std::string shell_quote(const std::string &src);

int run(const std::string &what, const std::vector<std::string> &argv);

/// This runs the executable given by the file name \p what.
/// Control returns when execution has finished.
/// Stdin, stdout and stderr may be redirected from/to a given file.
/// Give the empty std::string to retain the default handle.
/// Any shell-meta characters in the executable, \p argv and the I/O
/// redirect files are escaped as needed.
int run(
  const std::string &what,
  const std::vector<std::string> &argv,
  const std::string &std_input,
  const std::string &std_output,
  const std::string &std_error);

/// This runs the executable given by the file name \p what.
/// Control returns when execution has finished.
/// Stdin and stderr may be redirected from/to a given file.
/// Give the empty std::string to retain the default handle.
/// Any output to stdout is stored in the \p std_output stream buffer.
/// Any shell-meta characters in the executable, \p argv and the I/O
/// redirect files are escaped as needed.
int run(
  const std::string &what,
  const std::vector<std::string> &argv,
  const std::string &std_input,
  std::ostream &std_output,
  const std::string &std_error);

}
#endif // CVC5__RUN_H