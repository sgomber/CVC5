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

namespace CVC4 {
namespace theory {

Node Evaluator::eval(TNode n,
                     const std::vector<Node>& args,
                     const std::vector<Node>& vals)
{
  d_results.clear();
  d_hasResult = true;

  std::vector<TNode> queue;
  queue.emplace_back(n);

  while (queue.size() != 0)
  {
    TNode currNode = queue.back();

    if (d_results.find(currNode) != d_results.end())
    {
      queue.pop_back();
      continue;
    }

    bool doEval = true;
    for (const auto& currNodeChild : currNode)
    {
      if (d_results.find(currNodeChild) == d_results.end())
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
          return Node::null();
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
          lambdaVals.insert(lambdaVals.begin(), d_results[lambdaVal].toNode());
        }

        currNodeVal = eval(op[1], lambdaArgs, lambdaVals);
      }

      switch (currNodeVal.getKind())
      {
        case kind::CONST_BITVECTOR:
          d_results[currNode] = Result(currNodeVal.getConst<BitVector>());
          break;

        case kind::BITVECTOR_NOT:
          d_results[currNode] = Result(~d_results[currNode[0]].d_bv);
          break;

        case kind::BITVECTOR_NEG:
          d_results[currNode] = Result(-d_results[currNode[0]].d_bv);
          break;

        case kind::BITVECTOR_EXTRACT:
        {
          unsigned lo = bv::utils::getExtractLow(currNodeVal);
          unsigned hi = bv::utils::getExtractHigh(currNodeVal);
          d_results[currNode] =
              Result(d_results[currNode[0]].d_bv.extract(hi, lo));
          break;
        }

        case kind::BITVECTOR_CONCAT:
        {
          BitVector res = d_results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res.concat(d_results[currNode[i]].d_bv);
          }
          d_results[currNode] = Result(res);
          break;
        }

        case kind::BITVECTOR_PLUS:
        {
          BitVector res = d_results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res + d_results[currNode[i]].d_bv;
          }
          d_results[currNode] = Result(res);
          break;
        }

        case kind::BITVECTOR_MULT:
        {
          BitVector res = d_results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res * d_results[currNode[i]].d_bv;
          }
          d_results[currNode] = Result(res);
          break;
        }
        case kind::BITVECTOR_AND:
        {
          BitVector res = d_results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res & d_results[currNode[i]].d_bv;
          }
          d_results[currNode] = Result(res);
          break;
        }

        case kind::BITVECTOR_OR:
        {
          BitVector res = d_results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res | d_results[currNode[i]].d_bv;
          }
          d_results[currNode] = Result(res);
          break;
        }

        case kind::BITVECTOR_XOR:
        {
          BitVector res = d_results[currNode[0]].d_bv;
          for (size_t i = 1, end = currNode.getNumChildren(); i < end; i++)
          {
            res = res ^ d_results[currNode[i]].d_bv;
          }
          d_results[currNode] = Result(res);
          break;
        }

        case kind::EQUAL:
        {
          Result lhs = d_results[currNode[0]];
          Result rhs = d_results[currNode[1]];

          d_results[currNode] = Result(lhs.d_bv == rhs.d_bv);
          break;
        }

        case kind::ITE:
        {
          if (d_results[currNode[0]].d_bool)
          {
            d_results[currNode] = d_results[currNode[1]];
          }
          else
          {
            d_results[currNode] = d_results[currNode[2]];
          }
          break;
        }

        case kind::NOT:
        {
          d_results[currNode] = Result(!(d_results[currNode[0]].d_bool));
          break;
        }

        default:
        {
          Trace("evaluator") << "Kind " << currNodeVal.getKind()
                             << " not supported" << std::endl;
          d_results[currNode] = Result();
        }
      }
    }
  }

  return d_results[n].toNode();
}

}  // namespace theory
}  // namespace CVC4
