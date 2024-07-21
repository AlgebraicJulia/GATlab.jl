# """
# Defines Roe, a struct which acts as a wrapper for e-graph typed in the Sorts of a given theory, as well as functions for manipulating it.
# """
# module RoeUtility

# using ..SSAExtract: SSA, SSAVar, SSAExpr, extract_ssa!
using ..Util.HashColor

using StructEquality
import Metatheory
using Metatheory: EGraph, EGraphs, Id, VECEXPR_FLAG_ISCALL, VECEXPR_FLAG_ISTREE, VECEXPR_META_LENGTH
using MLStyle
using Reexport

"""
Sorts in each theory are subtypes of this abstract type.
"""
abstract type AbstractSort end
export AbstractSort

"""    TypedApplication

Struct containing a Function and the vector of Sorts it requires.
"""
@struct_hash_equal struct TypedApplication
    head::Function
    sorts::Vector{AbstractSort}
end
export TypedApplication

const TA = TypedApplication
export TA

Base.show(io::IO, ta::TA) = print(io, Expr(:call, nameof(ta.head), ta.sorts...))

struct SortError <: Exception
  message::String
end
export SortError

"""   RootVar

A childless node on an e-graph.

"""
@struct_hash_equal struct RootVar
    name::Symbol
    idx::Int
    sort::AbstractSort
end
export RootVar 

""" Roe

Struct for storing an EGraph and its variables.

Roe is the name for lobster eggs. "Egg" is the name of a Rust implementation of e-graphs, by which Metatheory.jl is inspired by. Lobsters are part of the family Decapodes, which is also the name of the AlgebraicJulia package which motivated this package. Hence, Roe.
"""
struct Roe
    variables::Vector{RootVar}
    graph::EGraph{Expr, AbstractSort}
    function Roe()
        new(RootVar[], EGraph{Expr, AbstractSort}())
    end
end
export Roe

"""

A struct containing a Roe and the Id of a variable in that EGraph. The type parameter for this struct is the variable it represents.

"""
struct Var{S}
    roe::Roe
    id::Id
end

function EGraphs.make(g::EGraph{Expr, AbstractSort}, n::Metatheory.VecExpr)
    op = EGraphs.get_constant(g,Metatheory.v_head(n))
    if op isa RootVar
        op.sort
    elseif op isa Number
        Scalar()
    else
        op((g[arg].data for arg in Metatheory.v_children(n))...)
    end
end
export make

function EGraphs.join(s1::AbstractSort, s2::AbstractSort)
    if s1 == s2
        s1
    else
        error("Cannot equate two nodes with different sorts")
    end
end
export join

function extract!(v::Var, f=EGraphs.astsize)
    extract!(v.roe.graph, f, v.id)
end
export extract!

function rootvarcrayon(v::RootVar)
  lightnessrange = (50., 100.)
  HashColor.hashcrayon(v.idx; lightnessrange, chromarange=(50., 100.))
end

function Base.show(io::IO, v::RootVar)
  if get(io, :color, true)
    crayon = rootvarcrayon(v)
    print(io, crayon, "$(v.name)")
    print(io, inv(crayon))
  else
    print(io, "$(v.name)#$(v.idx)")
  end    
end

"""   fix_functions(e)::Union{Symbol, Expr}

Traverses the AST of an expression, replacing the head of :call expressions to its name, a Symbol.
"""
function fix_functions(e)
    @match e begin
        s::Symbol => s
        Expr(:call, f::Function, args...) =>
          Expr(:call, nameof(f), fix_functions.(args)...)
        Expr(head, args...) =>
          Expr(head, fix_functions.(args)...)
        _ => e
    end
end

"""    getexpr(v::Var)::Union{Symbol, Expr}

Extracts an expression (::Var) from its Roe.

"""
function getexpr(v::Var)
    e = EGraphs.extract!(v.roe.graph, Metatheory.astsize, v.id)
    fix_functions(e)
end
export getexpr

function Base.show(io::IO, v::Var)
    print(io, getexpr(v))
end

"""    fresh!(roe::Roe, sort::AbstractSort, name::Symbol)::Var{sort}

Creates a new ("fresh") variable in a Roe given a sort and a name.

Example:
```
fresh!(roe, Form(0), :Temp)
```

"""
function fresh!(roe::Roe, sort::AbstractSort, name::Symbol)
    v = RootVar(name, length(roe.variables), sort)
    push!(roe.variables, v)
    n = Metatheory.v_new(0)
    Metatheory.v_set_head!(n, EGraphs.add_constant!(roe.graph, v))
    Metatheory.v_set_signature!(n, hash(Metatheory.maybe_quote_operation(v), hash(0)))
    Var{sort}(roe, EGraphs.add!(roe.graph, n, false))
end
export fresh!


@nospecialize
"""    inject_number!(roe::Roe, x::Number)::Var{Scalar()}

Adds a number to the Roe as a EGraph constant.

"""
function inject_number!(roe::Roe, x::Number)
    x = Float64(x)
    n = Metatheory.v_new(0)
    Metatheory.v_set_head!(n, EGraphs.add_constant!(roe.graph, x))
    Metatheory.v_set_signature!(n, hash(Metatheory.maybe_quote_operation(x), hash(0)))
    Var{Scalar()}(roe, EGraphs.add!(roe.graph, n, false))
end
export inject_number!

@nospecialize
"""    addcall!(g::EGraph, head, args)::

Adds a call to an EGraph.

"""
function addcall!(g::EGraph, head, args)
    ar = length(args)
    n = Metatheory.v_new(ar)
    Metatheory.v_set_flag!(n, VECEXPR_FLAG_ISTREE)
    Metatheory.v_set_flag!(n, VECEXPR_FLAG_ISCALL)
    Metatheory.v_set_head!(n, EGraphs.add_constant!(g, head))
    Metatheory.v_set_signature!(n, hash(Metatheory.maybe_quote_operation(head), hash(ar)))
    for i in Metatheory.v_children_range(n)
        @inbounds n[i] = args[i - VECEXPR_META_LENGTH]
    end
    EGraphs.add!(g, n, false)
end
export addcall!

"""    equate!(v1::Var{s1}, v2::Var{s2})::EGraph

Asserts that two variables of the same e-graph are the same. This is done by returning the union of the variable ids with the e-graph.
"""
function equate!(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    (s1 == s2) || throw(SortError("Cannot equate variables of a different sort: attempted to equate $s1 with $s2"))
    v1.roe === v2.roe || error("Cannot equate variables from different graphs")
    union!(v1.roe.graph, v1.id, v2.id)
end
export equate!

"""
Infix synonym for `equate!`
"""
≐(v1::Var, v2::Var) = equate!(v1, v2)
export ≐

# end
