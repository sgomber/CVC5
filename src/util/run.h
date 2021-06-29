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

using namespace std;

namespace cvc5 {
/// This performs shell quoting if necessary on input \p src.
string shell_quote(const string &src);

int run(const string &what, const vector<string> &argv);

/// This runs the executable given by the file name \p what.
/// Control returns when execution has finished.
/// Stdin, stdout and stderr may be redirected from/to a given file.
/// Give the empty string to retain the default handle.
/// Any shell-meta characters in the executable, \p argv and the I/O
/// redirect files are escaped as needed.
int run(
  const string &what,
  const vector<string> &argv,
  const string &std_input,
  const string &std_output,
  const string &std_error);

/// This runs the executable given by the file name \p what.
/// Control returns when execution has finished.
/// Stdin and stderr may be redirected from/to a given file.
/// Give the empty string to retain the default handle.
/// Any output to stdout is stored in the \p std_output stream buffer.
/// Any shell-meta characters in the executable, \p argv and the I/O
/// redirect files are escaped as needed.
int run(
  const string &what,
  const vector<string> &argv,
  const string &std_input,
  ostream &std_output,
  const string &std_error);

}
#endif // CVC5__RUN_H