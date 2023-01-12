/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Encapsulation of the result of a synthesis query.
 */

#include "cvc5_public.h"

#ifndef CVC5__UTIL__OMT_RESULT_H
#define CVC5__UTIL__OMT_RESULT_H

#include <iosfwd>
#include <string>

#include "util/result.h"

namespace cvc5::internal {

/**
 * A result for a synthesis query. This can be used for synthesis, abduction,
 * interpolation, and quantifier elimination.
 */
class OmtResult
{
 public:
  enum Status
  {
    // the status has not been set
    NONE,
    OPTIMAL,
    NON_OPTIMAL,
    UNSAT,
    UNKNOWN
  };

 public:
  /** Default constructor */
  OmtResult();
  /** Constructor when the solution is not successful */
  OmtResult(Status s,
              UnknownExplanation unknownExplanation =
                  UnknownExplanation::UNKNOWN_REASON);

  /** Get the status */
  Status getStatus() const;

  /** Get the unknown explanation */
  UnknownExplanation getUnknownExplanation() const;

  /** Get the string representation */
  std::string toString() const;

 private:
  /** The status */
  Status d_status;
  /** The unknown explanation */
  UnknownExplanation d_unknownExplanation;
};

std::ostream& operator<<(std::ostream& out, const OmtResult& r);
std::ostream& operator<<(std::ostream& out, OmtResult::Status s);

}  // namespace cvc5::internal

#endif /* CVC5__RESULT_H */
