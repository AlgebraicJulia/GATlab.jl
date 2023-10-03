module GATs
export Constant, AlgTerm, AlgType,
  TypeScope, TypeCtx, AlgSort, AlgSorts,
  AlgDeclaration, AlgTermConstructor, AlgTypeConstructor, AlgAccessor, AlgAxiom,
  sortsignature, getdecl,
  GATSegment, GAT, GATContext, allmethods,
  termcons, typecons, accessors,
  equations, build_infer_expr, compile, sortcheck, allnames, sorts, sortname,
  InCtx, TermInCtx, TypeInCtx, headof, argsof, argcontext

using ..Scopes
import ..ExprInterop: fromexpr, toexpr

import ..Scopes: retag, rename

using StructEquality
using MLStyle

include("gats/ast.jl")
include("gats/judgments.jl")
include("gats/gat.jl")
include("gats/exprinterop.jl")
include("gats/algorithms.jl")

end
