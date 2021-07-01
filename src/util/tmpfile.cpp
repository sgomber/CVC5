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

#include "tmpfile.h"
#include <filesystem>


#include <cstdlib>
#include <cstring>

#include "system_exception.h"
#include <unistd.h>


namespace cvc5 {

/// Substitute for mkstemps (OpenBSD standard) for Windows, where it is
/// unavailable. 

std::string get_temporary_file(
  const std::string &prefix,
  const std::string &suffix)
{
  std::string dir="/tmp/";
  const char *TMPDIR_env=getenv("TMPDIR");
  if(TMPDIR_env!=nullptr)
    dir=TMPDIR_env;
  if(*dir.rbegin()!='/')
    dir+='/';

  std::string t_template=
    dir+prefix+std::to_string(getpid())+".XXXXXX"+suffix;

  char *t_ptr=strdup(t_template.c_str());

  int fd=mkstemps(t_ptr, suffix.size());

  if(fd<0)
    throw cvc5::SystemException("Failed to open temporary file");

  close(fd);

  std::string result=std::string(t_ptr);
  free(t_ptr);
  return result;
}

temporary_filet::~temporary_filet()
{
  if(!name.empty())
    std::filesystem::remove(name);
}

}