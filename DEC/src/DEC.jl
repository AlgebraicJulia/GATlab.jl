module DEC

using Reexport

using MLStyle
using Reexport
using StructEquality
import Metatheory
using Metatheory: EGraph, EGraphs, Id, astsize
using Metatheory: VECEXPR_FLAG_ISCALL, VECEXPR_FLAG_ISTREE, VECEXPR_META_LENGTH
import Metatheory: extract!

import Base: +, -, *

include("util/module.jl") # Pretty-printing
include("roe.jl") # Checking signature for DEC operations
include("SSAs.jl") # manipulating SSAs 
include("vfield.jl") # producing a vector field function

# currently this only holds the DEC
include("theories/module.jl")

@reexport using .Util
@reexport using .SSAs
@reexport using .Theories

# function vfield(model, operator_lookup::Dict{TA, Any})
#     roe = Roe(DEC.ThDEC.Sort)

#     (state_vars, param_vars) = model(roe)
#     length(state_vars) >= 1 || error("need at least one state variable in order to create vector field")
#     state_rootvars = map(state_vars) do x
#       rv = extract!(x)
#       rv isa RootVar ? rv : error("all state variables must be RootVars")
#     end
#     param_rootvars = map(param_vars) do p
#       rv = extract!(p)
#       rv isa RootVar ? rv : error("all param variables must be RootVars")
#     end

#     u = :u
#     p = :p
#     du = :du

#     rootvar_lookup =
#     Dict{RootVar, Tuple{Union{Expr, Symbol}, Bool}}(
#             [
#                [rv => (:($(u)), false) for rv in state_rootvars];
#                [rv => (:($(p)), true) for rv in param_rootvars]
#             ]
#         )

#     cost = derivative_cost(Set([state_rootvars; param_rootvars]))

#     extractor = EGraphs.Extractor(roe.graph, cost, Float64)

#     function term_select(id)
#       EGraphs.find_best_node(extractor, id)
#     end

#     ssa = SSA()

#     # TODO overload extract! to index by graph
#     derivative_vars = map(state_vars) do v
#       extract!(roe.graph, ssa, (∂ₜ(v)).id, term_select)
#     end

#     toexpr(v::DEC.SSAs.Var) = Symbol("tmp%$(v.idx)")

#     function toexpr(expr::Term)
#       @match expr.head begin
#         ::RootVar => @match rootvar_lookup[expr.head] begin
#           (v, false) => v
#           # evaluates in DEC.k, and this gets the index
#           (v, true) => Expr(:ref, v, expr.head.name)
#         end
#         ::Number => expr.head
#         _ => begin
#           op = get(operator_lookup, TA(expr.head, first.(expr.args)))
#           # Decapode operators return a tuple of functions. We choose the first of these.
#           if op isa Tuple
#             op = op[1]
#           end
#           Expr(:call, *, op, toexpr.(last.(expr.args))...)
#         end
#       end
#     end

#     ssalines = map(enumerate(ssa.statements)) do (i, expr)
#       :($(toexpr(SSAs.Var(i))) = $(toexpr(expr)))
#     end

#     set_derivative_stmts = map(enumerate(derivative_vars)) do (i, v)
#       :($(du) .= $(toexpr(v)))
#     end

#     # yield function 
#     eval(quote
#       f(du, u, p, _) = begin
#         $(ssalines...)
#         $(set_derivative_stmts...)
#       end
#   end)
# end
# export vfield

end
