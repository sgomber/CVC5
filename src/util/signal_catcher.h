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
 * Won't work for windows
 */

#ifndef CVC5__SIGNAL_CATCHER_H
#define CVC5__SIGNAL_CATCHER_H
#include <csignal>

namespace cvc5 {

void install_signal_catcher();
void remove_signal_catcher();
void signal_catcher(int sig);

void register_child(pid_t);
void unregister_child();
}  // namespace cvc5

#endif  // CVC5__SIGNAL_CATCHER_H