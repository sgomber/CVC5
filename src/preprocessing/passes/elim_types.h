/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The eliminate types preprocessing pass.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__ELIM_TYPES_H
#define CVC5__PREPROCESSING__PASSES__ELIM_TYPES_H

#include <map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "expr/node.h"
#include "expr/node_converter.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

class ElimTypesNodeConverter : public NodeConverter
{
 public:
  ElimTypesNodeConverter() {}
  Node preConvert(Node n) override;
  Node postConvert(Node n, const std::vector<Node>& ncs) override;
  TypeNode postConvertType(TypeNode tn) override;
  /** Split */
  void addElimDatatype(TypeNode dtn);
  /** Empty */
  bool empty() const;

 private:
  /** get or mk split terms */
  const std::vector<Node>& getOrMkSplitTerms(Node n);
  /** inline arguments */
  std::vector<Node> inlineArguments(const std::vector<Node>& args);
  /** mapped index */
  size_t getMappedDatatypeIndex(Node n) const;
  /** return convert */
  Node returnConvert(Node n, Node ret);
  /** Split 1-cons */
  std::map<TypeNode, std::vector<TypeNode>> d_splitDt;
  /** the selector chain for each type */
  std::map<TypeNode, std::vector<Node>> d_splitDtSelc;
  /** Splits */
  std::map<Node, std::vector<Node>> d_splitDtTerms;
  /** dt index */
  std::map<Node, size_t> d_dtIndex;
};

class ElimTypes : public PreprocessingPass
{
  using TypeNodeMap =
      context::CDHashMap<TypeNode, TypeNode>;
  using NodeMap = context::CDHashMap<Node, Node>;

 public:
  ElimTypes(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /** Collect types in node n */
  void collectTypes(const Node& n,
                    std::unordered_set<TNode>& visited,
                    std::unordered_set<TypeNode>& types,
                    std::map<TypeNode, std::vector<Node>>& sym);
  /** Simplify type */
  TypeNode simplifyType(TypeNode tn);
  /** Simplify */
  Node simplify(const Node& n);
  /** A node converter */
  ElimTypesNodeConverter d_etnc;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5

#endif /* CVC5__PREPROCESSING__PASSES__ELIM_TYPES_H */
