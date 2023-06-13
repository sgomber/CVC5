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
 * Runs system commands. Won't work for windows
 */

#ifndef CVC5__RUN_H
#define CVC5__RUN_H

#include <cvc5/cvc5_export.h>

#include <iosfwd>
#include <string>
#include <vector>

namespace cvc5 {
/// This performs shell quoting if necessary on input \p src.
std::string shell_quote(const std::string& src);

int run(const std::string& what, const std::vector<std::string>& argv);

/// This runs the executable given by the file name \p what.
/// Control returns when execution has finished.
/// Stdin, stdout and stderr may be redirected from/to a given file.
/// Give the empty std::string to retain the default handle.
/// Any shell-meta characters in the executable, \p argv and the I/O
/// redirect files are escaped as needed.
int run(const std::string& what,
        const std::vector<std::string>& argv,
        const std::string& std_input,
        const std::string& std_output,
        const std::string& std_error);

/// This runs the executable given by the file name \p what.
/// Control returns when execution has finished.
/// Stdin and stderr may be redirected from/to a given file.
/// Give the empty std::string to retain the default handle.
/// Any output to stdout is stored in the \p std_output stream buffer.
/// Any shell-meta characters in the executable, \p argv and the I/O
/// redirect files are escaped as needed.
int run(const std::string& what,
        const std::vector<std::string>& argv,
        const std::string& std_input,
        std::ostream& std_output,
        const std::string& std_error) CVC5_EXPORT;

}  // namespace cvc5
#endif  // CVC5__RUN_H