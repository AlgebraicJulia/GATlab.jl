module DEC
using MLStyle
using StructEquality
import Metatheory
using Metatheory: EGraph, EGraphs, Id, VECEXPR_FLAG_ISCALL, VECEXPR_FLAG_ISTREE, VECEXPR_META_LENGTH
import Metatheory: extract!

import Base: +, -
import Base: *

include("HashColor.jl")

@data Sort begin
    Scalar()
    Form(dim::Int, isdual::Bool)
end
export Scalar, Form, DualForm

struct SortError <: Exception
    message::String
end

@nospecialize
function +(s1::Sort, s2::Sort)
    @match (s1, s2) begin
        (Scalar(), Scalar()) => Scalar()
        (Scalar(), Form(d, isdual)) || (Form(d, isdual), Scalar()) => Form(d, isdual)
        (Form(d, ϖ), Form(d′, ϖ′)) =>
          if (d == d′) && (ϖ == ϖ′)
            Form(d, ϖ)
          else
            throw(SortError("Cannot add two forms of different dimensions/dualities $(d,ϖ) and $(d′,ϖ′)"))
          end
    end
end

-(s1::Sort, s2::Sort) = +(s1, s2)

-(s::Sort) = s

@nospecialize
function *(s1::Sort, s2::Sort)
  @match (s1, s2) begin
    (Scalar(), Scalar()) => Scalar()
    (Scalar(), Form(d, ϖ)) || (Form(d, ϖ), Scalar()) => Form(d)
    (Form(_, _), Form(_, _)) => throw(SortError("Cannot multiply two forms. Maybe try `∧`??"))
  end
end

@nospecialize
function ∧(s1::Sort, s2::Sort)
    @match (s1, s2) begin
        (_, Scalar()) || (Scalar(), _) => throw(SortError("Cannot take a wedge product with a scalar"))
        (Form(d, ϖ), Form(d′, ϖ)) =>
          if d + d′ <= 2l
            Form(d + d′)
          else
            throw(SortError("Can only take a wedge product when the dimensions of the forms add to less than 2: tried to wedge product $d and $(d′)"))
          end
    end
end

@nospecialize
∂ₜ(s::Sort) = s

@nospecialize
function d(s::Sort)
    @match s begin
        Scalar() => throw(SortError("Cannot take exterior derivative of a scalar"))
        Form(d) =>
          if d <= 1
            Form(d + 1)
          else
            throw(SortError("Cannot take exterior derivative of a n-form for n >= 1"))
          end
    end
end

@struct_hash_equal struct RootVar
    name::Symbol
    idx::Int
    sort::Sort
end

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
    print(io, "$(v.name)%$(v.idx)")
  end    
end

struct Decapode
    variables::Vector{RootVar}
    graph::EGraph{Expr, Sort}
    function Decapode()
        new(RootVar[], EGraph{Expr, Sort}())
    end
end

struct Var{S}
    pode::Decapode
    id::Id
end

function extract!(v::Var, f=EGraphs.astsize)
    extract!(v.pode.graph, f, v.id)
end

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

function getexpr(v::Var)
    e = EGraphs.extract!(v.pode.graph, Metatheory.astsize, v.id)
    fix_functions(e)
end

function Base.show(io::IO, v::Var)
    print(io, getexpr(v))
end

function fresh!(d::Decapode, sort::Sort, name::Symbol)
    v = RootVar(name, length(d.variables), sort)
    push!(d.variables, v)
    n = Metatheory.v_new(0)
    Metatheory.v_set_head!(n, EGraphs.add_constant!(d.graph, v))
    Metatheory.v_set_signature!(n, hash(Metatheory.maybe_quote_operation(v), hash(0)))
    Var{sort}(d, EGraphs.add!(d.graph, n, false))
end

@nospecialize
function inject_number!(d::Decapode, x::Number)
    x = Float64(x)
    n = Metatheory.v_new(0)
    Metatheory.v_set_head!(n, EGraphs.add_constant!(d.graph, x))
    Metatheory.v_set_signature!(n, hash(Metatheory.maybe_quote_operation(x), hash(0)))
    Var{Scalar()}(d, EGraphs.add!(d.graph, n, false))
end

@nospecialize
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

@nospecialize
function +(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    v1.pode === v2.pode || error("Cannot add variables from different graphs")
    s = s1 + s2
    Var{s}(v1.pode, addcall!(v1.pode.graph, +, (v1.id, v2.id)))
end

@nospecialize
+(v::Var, x::Number) = +(v, inject_number!(v.pode, x))

@nospecialize
+(x::Number, v::Var) = +(inject_number!(v.pode, x), v)

@nospecialize
function -(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    v1.pode == v2.pode || error("Cannot subtract variables from different graphs")
    s = s1 - s2
    Var{s}(v1.pode, addcall!(v1.pode.graph, -, (v1.id, v2.id)))
end

@nospecialize
-(v::Var{s}) where {s} = Var{s}(v.pode, addcall!(v.pode.graph, -, (v.id,)))

@nospecialize
-(v::Var, x::Number) = -(v, inject_number!(v.pode, x))

@nospecialize
-(x::Number, v::Var) = -(inject_number!(v.pode, x), v)

@nospecialize
function *(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    v1.pode === v2.pode || error("Cannot multiply variables from different graphs")
    s = s1 * s2
    Var{s}(v1.pode, addcall!(v1.pode.graph, *, (v1.id, v2.id)))
end

@nospecialize
*(v::Var, x::Number) = *(v, inject_number!(v.pode, x))

@nospecialize
*(x::Number, v::Var) = *(inject_number!(v.pode, x), v)

@nospecialize
function ∧(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    v1.pode === v2.pode || error("Cannot wedge variables from different graphs")
    s = s1 ∧ s2
    Var{s}(v1.pode, addcall!(v1.pode.graph, ∧, (v1.id, v2.id)))
end

@nospecialize
function ∂ₜ(v::Var{s}) where {s}
    Var{s}(v.pode, addcall!(v.pode.graph, ∂ₜ, (v.id,)))
end

@nospecialize
function d(v::Var{s}) where {s}
    s′ = d(s)
    Var{s′}(v.pode, addcall!(v.pode.graph, d, (v.id,)))
end

function equate!(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    (s1 == s2) || throw(SortError("Cannot equate variables of a different sort: attempted to equate $s1 with $s2"))
    v1.pode === v2.pode || error("Cannot equate variables from different graphs")
    union!(v1.pode.graph, v1.id, v2.id)
end

≐(v1::Var, v2::Var) = equate!(v1, v2)

@nospecialize
function derivative_cost(allowed_roots)
    function cost(n::Metatheory.VecExpr, op, costs)
        if op == ∂ₜ || (op isa RootVar && op ∉ allowed_roots) 
            Inf
        else
            Metatheory.astsize(n, op, costs)
        end
    end
end

""" vfield :: (Decapode -> (StateVars, ParamVars)) -> VectorFieldFunction

Short for "vector field." Obtains tuple of root vars from a model, where the first component are state variables and the second are parameter variables.

Example: given a diffusivity constant a, the heat equation can be written as:
```
  ∂ₜ u = a * Laplacian(u)
```
would return (u, a).

A limitation of this function can be demonstrated here: given the model
  ```
    ∂ₜ a = a + b
    ∂ₜ b = a + b
  ```
  we would return ([a, b],). Suppose we wanted to extract terms of the form "a + b." Since the expression "a + b" is not a RootVar, 
  the extractor would bypass it completely.
"""
function vfield(model)
    pode = Decapode()
    (state_vars, param_vars) = model(pode)
    length(state_vars) >= 1 || error("need at least one state variable in order to create vector field")
    state_rootvars = map(state_vars) do x
        rv = extract!(x)
        rv isa RootVar || error("all state variables must be RootVars")
        rv
    end
    param_rootvars = map(param_vars) do p
        rv = extract!(p)
        rv isa RootVar || error("all state variables must be RootVars")
        rv
    end
    cost = derivative_cost(Set([state_rootvars; param_rootvars]))

    u = :u
    p = :p
    du = :du

    rootvar_lookup =
        Dict{RootVar, Expr}(
            [
                [rv => :(@inbounds $(u)[$i]) for (i, rv) in enumerate(state_rootvars)];
                [rv => :(@inbounds $(p)[$i]) for (i, rv) in enumerate(param_rootvars)]
            ]
        )

    derivative_exprs = map(enumerate(state_vars)) do (i, v)
        e = extract!(∂ₜ(v), cost)
        :(@inbounds $(du)[$i] = $(replace_rootvars(e, rootvar_lookup)))
    end

    eval(
        quote
            ($du, $u, $p, _) -> begin
                $(derivative_exprs...)
                $du
            end
        end
    )
end

function replace_rootvars(e, rootvar_lookup::Dict{RootVar, Expr})
    @match e begin
        (rv::RootVar) => rootvar_lookup[rv]
        Expr(head, args...) => Expr(head, replace_rootvars.(args, Ref(rootvar_lookup))...)
        _ => e
    end
end

end # module DEC
