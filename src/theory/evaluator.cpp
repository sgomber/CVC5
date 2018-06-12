/*********************                                                        */
/*! \file evaluator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The Evaluator class
 **
 ** The Evaluator class.
 **/

#include "theory/evaluator.h"

#include "theory/bv/theory_bv_utils.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {

Node Evaluator::eval(TNode n,
                     const std::vector<Node>& args,
                     const std::vector<Node>& vals)
{
  Trace("evaluator") << "Evaluating " << n << " under substitution " << args
                     << " " << vals << std::endl;
  return evalInternal(n, args, vals).toNode();
}

Result Evaluator::evalInternal(TNode n,
                               const std::vector<Node>& args,
                               const std::vector<Node>& vals)
{
  std::unordered_map<TNode, Result, TNodeHashFunction> results;
  std::vector<TNode> queue;
  queue.emplace_back(n);

  while (queue.size() != 0)
  {
    TNode currNode = queue.back();

    if (results.find(currNode) != results.end())
    {
      queue.pop_back();
      continue;
    }

    bool doEval = true;
    for (const auto& currNodeChild : currNode)
    {
      if (results.find(currNodeChild) == results.end())
      {
        queue.emplace_back(currNodeChild);
        doEval = false;
      }
    }

    if (doEval)
    {
      queue.pop_back();

      Node currNodeVal = currNode;
      if (currNode.isVar())
      {
        const auto& it = std::find(args.begin(), args.end(), currNode);

        if (it == args.end())
        {
          return Result();
        }

        ptrdiff_t pos = std::distance(args.begin(), it);
        currNodeVal = vals[pos];
      }
      else if (currNode.getKind() == kind::APPLY_UF
               && currNode.getOperator().getKind() == kind::LAMBDA)
      {
        std::vector<Node> lambdaArgs(args);
        std::vector<Node> lambdaVals(vals);

        Node op = currNode.getOperator();
        for (const auto& lambdaArg : op[0])
        {
          lambdaArgs.insert(lambdaArgs.begin(), lambdaArg);
        }

        for (const auto& lambdaVal : currNode)
        {
          lambdaVals.insert(lambdaVals.begin(), results[lambdaVal].toNode());
        }

        results[currNode] = evalInternal(op[1], lambdaArgs, lambdaVals);
        continue;
      }

      switch (currNodeVal.getKind())
      {
        case kind::CONST_BITVECTOR:
          results[currNode] = Result(currNodeVal.getConst<BitVector>());
          break;

        case kind::BITVECTOR_NOT:
          results[currNode] = Result(~results[currNode[0]].d_bv);
          break;

        case kind::BITVECTOR_NEG:
          results[currNode] = Result(-results[currNode[0]].d_bv);
          break;

        case kind::BITVECTOR_EXTRACT:
        {
          unsigned lo = bv::utils::getExtractLow(currNodeVal);
          unsigned hi = bv::utils::getExtractHigh(currNodeVal);
          results[currNode] = Result(results[currNode[0]].d_bv.extract(hi, lo));
          break;
        }

        case kind::BITVECTOR_CONCAT:
        {
          BitVector res = results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res.concat(results[currNode[i]].d_bv);
          }
          results[currNode] = Result(res);
          break;
        }

        case kind::BITVECTOR_PLUS:
        {
          BitVector res = results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res + results[currNode[i]].d_bv;
          }
          results[currNode] = Result(res);
          break;
        }

        case kind::BITVECTOR_MULT:
        {
          BitVector res = results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res * results[currNode[i]].d_bv;
          }
          results[currNode] = Result(res);
          break;
        }
        case kind::BITVECTOR_AND:
        {
          BitVector res = results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res & results[currNode[i]].d_bv;
          }
          results[currNode] = Result(res);
          break;
        }

        case kind::BITVECTOR_OR:
        {
          BitVector res = results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res | results[currNode[i]].d_bv;
          }
          results[currNode] = Result(res);
          break;
        }

        case kind::BITVECTOR_XOR:
        {
          BitVector res = results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res ^ results[currNode[i]].d_bv;
          }
          results[currNode] = Result(res);
          break;
        }

        case kind::EQUAL:
        {
          Result lhs = results[currNode[0]];
          Result rhs = results[currNode[1]];

          switch (lhs.d_tag)
          {
            case Result::BOOL:
            {
              results[currNode] = Result(lhs.d_bool == rhs.d_bool);
              break;
            }

            case Result::BITVECTOR:
            {
              results[currNode] = Result(lhs.d_bv == rhs.d_bv);
              break;
            }

            default:
            {
              Trace("evaluator") << "Theory " << Theory::theoryOf(currNode[0])
                                 << " not supported" << std::endl;
              results[currNode] = Result();
              break;
            }
          }

          break;
        }

        case kind::ITE:
        {
          if (results[currNode[0]].d_bool)
          {
            results[currNode] = results[currNode[1]];
          }
          else
          {
            results[currNode] = results[currNode[2]];
          }
          break;
        }

        case kind::NOT:
        {
          results[currNode] = Result(!(results[currNode[0]].d_bool));
          break;
        }

        default:
        {
          Trace("evaluator") << "Kind " << currNodeVal.getKind()
                             << " not supported" << std::endl;
          results[currNode] = Result();
        }
      }
    }
  }

  return results[n];
}

}  // namespace theory
}  // namespace CVC4
