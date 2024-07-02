module GATs
export Constant, AlgTerm, AlgType, AlgAST,
  TypeScope, TypeCtx, AlgSort, AlgEqSort, AlgSorts,
  AlgDeclaration, AlgTermConstructor, AbstractAlgSort,
  AlgTypeConstructor, AlgAccessor, AlgAxiom, AlgStruct, AlgDot, AlgFunction,
  typesortsignature, sortsignature, getdecl,
  GATSegment, GAT, GATContext, gettheory, gettypecontext, allmethods, 
  resolvemethod,
  termcons,typecons, accessors, structs, primitive_sorts, struct_sorts,
  equations, build_infer_expr, compile, sortcheck, allnames, sorts, sortname,
  InCtx, TermInCtx, TypeInCtx, headof, argsof, methodof, bodyof, argcontext,
  infer_type

using ..Scopes
import ..ExprInterop: fromexpr, toexpr

import ..Scopes: retag, rename, reident

import AlgebraicInterfaces: equations

using StructEquality
using MLStyle
using DataStructures: OrderedDict

include("gats/ast.jl")
include("gats/judgments.jl")
include("gats/gat.jl")
include("gats/exprinterop.jl")
include("gats/algorithms.jl")

end
