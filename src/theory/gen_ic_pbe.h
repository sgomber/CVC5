/*********************                                                        */
/*! \file gen_ic_pbe.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief gen_ic_pbe
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__GEN_IC_PBE_H
#define __CVC4__THEORY__GEN_IC_PBE_H

#include <map>

namespace CVC4 {
namespace theory {

/** GenIcPbe
 * 
 */
class GenIcPbe 
{
public:
  GenIcPbe();
  ~GenIcPbe(){}
  /** run */
  void run();
};

} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__GEN_IC_PBE_H */
