/******************************************************************************
 * (C) 2001-2016, Daniel Kroening, Edmund Clarke,
 * Computer Science Department, University of Oxford
 * Computer Science Department, Carnegie Mellon University
 * 
 *  This file is adapted from CBMC utils https://github.com/diffblue/cbmc/util
 *
 * ****************************************************************************
 *
 *  
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
}

#endif // CVC5__SIGNAL_CATCHER_H