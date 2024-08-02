module SSAs

using ..DEC: AbstractSort, TypedApplication, TA, Roe, RootVar

# other dependencies
using MLStyle
using StructEquality
using Metatheory: VecExpr
using Metatheory.EGraphs
import Metatheory: extract!

"""    Var

A wrapper for the index of a Var
"""
@struct_hash_equal struct Var
  idx::Int
end
export Var

function Base.show(io::IO, v::Var)
  print(io, "%", v.idx)
end

"""    Term

A wrapper for a function (::Any) and its args (::Vector{Tuple{Sort, Var}}).

Example: the equation
```
  a = 1 + b
```
may have an SSA dictionary
```
  %1 => a
  %2 => +(%1, %3)
  %3 => b
```
and so `+` would have
```
Term(+, [(Scalar(), Var(1)), (Scalar(), Var(2))])
```
"""
@struct_hash_equal struct Term
  head::Any
  args::Vector{Tuple{AbstractSort, Var}}
end
export Term

function Base.show(io::IO, e::Term)
  print(io, e.head)
  if length(e.args) > 0
    print(io, Expr(:tuple, (Expr(:(::), v, sort) for (sort, v) in e.args)...))
  end
end

"""

Struct defining Static Single-Assignment information for a given roe.

Advantages of SSA form:

1. We can preallocate each matrix
2. We can run a register-allocation algorithm to minimize the number of matrices that we have to preallocate
"""
struct SSA
  assignment_lookup::Dict{Id, Var}
  statements::Vector{Term}
  function SSA()
    new(Dict{Id, Var}(), Term[])
  end
end
export SSA

# accessors
statements(ssa::SSA) = ssa.statements
export statements

# show methods

function Base.show(io::IO, ssa::SSA)
  println(io, "SSA: ")
  for (i, expr) in enumerate(statements(ssa))
    println(io, "  ", Var(i), " = ", expr)
  end
end

"""    add_stmt!(ssa::SSA, id::Id, expr::Term)::Var

Low-level function which, given an SSA, adds a Term onto the assignment_lookup. Users should use `extract!` instead. 

"""
function add_stmt!(ssa::SSA, id::Id, expr::Term)
  push!(ssa.statements, expr)
  v = Var(length(ssa.statements))
  ssa.assignment_lookup[id] = v
  v
end

Base.contains(ssa::SSA, id::Id) = haskey(ssa.assignment_lookup, id)
export contains

Base.getindex(ssa::SSA, id::Id) = ssa.assignment_lookup[id]
export getindex

"""
    extract!(g::EGraph, ssa::SSA, id::Id, term_select, make_expr)::Var

This function adds (recursively) the necessary lines to the SSA in order to
compute a value for `id`, and then returns the Var that the value for `id`
will be assigned to.

The closure parameters control the behavior of this function.

    term_select(id::Id)::VecExpr

This closure selects, given an id in an EGraph, the term that we want to use in
order to compute a value for that id

"""
function extract!(g::EGraph, ssa::SSA, id::Id, term_select)
  if contains(ssa, id)
    return getindex(ssa, id)
  end
  term = term_select(id)
  args = map(EGraphs.v_children(term)) do arg
    (g[arg].data, extract!(g, ssa, arg, term_select))
  end
  add_stmt!(ssa, id, Term(EGraphs.get_constant(g, EGraphs.v_head(term)), args))
end
export extract!

function extract!(g::EGraph, id::Id; ssa::SSA=SSA(), term_select::Function=best_term)
  extract!(g, ssa, id, term_select)
end

function extract!(roe::Roe{S}, id::Id; ssa::SSA=SSA(), term_select::Function=best_term) where S
  extract!(roe, ssa, id, term_select)
end

end
