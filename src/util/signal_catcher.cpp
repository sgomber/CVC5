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


#include "signal_catcher.h"
#include <assert.h>


#include <cstdlib>


namespace cvc5 {

// Here we have an instance of an ugly global object.
// It keeps track of any child processes that we'll kill
// when we are told to terminate. "No child" is indicated by '0'.

pid_t child_pid = 0;

void register_child(pid_t pid)
{
  assert(child_pid == 0);
  child_pid = pid;
}

void unregister_child()
{
  assert(child_pid != 0);
  child_pid = 0;
}


void install_signal_catcher()
{
  // declare act to deal with action on signal set
  // NOLINTNEXTLINE(readability/identifiers)
  static struct sigaction act;

  act.sa_handler = signal_catcher;
  act.sa_flags = 0;
  sigfillset(&(act.sa_mask));

  // install signal handler
  sigaction(SIGTERM, &act, nullptr);

}

void remove_signal_catcher()
{
  // declare act to deal with action on signal set
  // NOLINTNEXTLINE(readability/identifiers)
  static struct sigaction act;

  act.sa_handler = SIG_DFL;
  act.sa_flags = 0;
  sigfillset(&(act.sa_mask));

  sigaction(SIGTERM, &act, nullptr);
}

void signal_catcher(int sig)
{
#if 0
  // kill any children by killing group
  killpg(0, sig);
#else
  // pass on to our child, if any
  if(child_pid != 0)
    kill(child_pid, sig);
#endif

  exit(sig); // should contemplate something from sysexits.h
}

}