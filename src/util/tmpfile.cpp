/******************************************************************************
 * (C) 2001-2016, Daniel Kroening, Edmund Clarke,
 * Computer Science Department, University of Oxford
 * Computer Science Department, Carnegie Mellon University
 * 
 *  This file is adapted from CBMC utils https://github.com/diffblue/cbmc/util
 *
 * ****************************************************************************
 *
 *  Creates tmp files. Won't work for windows
 */

#include "tmpfile.h"
#include <filesystem>


#include <cstdlib>
#include <cstring>

#include "system_exception.h"
#include <unistd.h>


using namespace std;
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
    filesystem::remove(name);
}

}