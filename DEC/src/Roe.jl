@struct_hash_equal struct RootVar
    name::Symbol
    idx::Int
    sort::Sort
end

struct Roe
    variables::Vector{RootVar}
    graph::EGraph{Expr, Sort}
    function Roe()
        new(RootVar[], EGraph{Expr, Sort}())
    end
end

struct Var{S}
    roe::Roe
    id::Id
end

function EGraphs.make(g::EGraph{Expr, Sort}, n::Metatheory.VecExpr)
    op = EGraphs.get_constant(g,Metatheory.v_head(n))
    if op isa RootVar
        op.sort
    elseif op isa Number
        Scalar()
    else
        op((g[arg].data for arg in Metatheory.v_children(n))...)
    end
end

function EGraphs.join(s1::Sort, s2::Sort)
    if s1 == s2
        s1
    else
        error("Cannot equate two nodes with different sorts")
    end
end

function extract!(v::Var, f=EGraphs.astsize)
    extract!(v.roe.graph, f, v.id)
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
    print(io, "$(v.name)#$(v.idx)")
  end    
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
    e = EGraphs.extract!(v.roe.graph, Metatheory.astsize, v.id)
    fix_functions(e)
end

function Base.show(io::IO, v::Var)
    print(io, getexpr(v))
end

function fresh!(roe::Roe, sort::Sort, name::Symbol)
    v = RootVar(name, length(roe.variables), sort)
    push!(roe.variables, v)
    n = Metatheory.v_new(0)
    Metatheory.v_set_head!(n, EGraphs.add_constant!(roe.graph, v))
    Metatheory.v_set_signature!(n, hash(Metatheory.maybe_quote_operation(v), hash(0)))
    Var{sort}(roe, EGraphs.add!(roe.graph, n, false))
end

@nospecialize
function inject_number!(roe::Roe, x::Number)
    x = Float64(x)
    n = Metatheory.v_new(0)
    Metatheory.v_set_head!(n, EGraphs.add_constant!(roe.graph, x))
    Metatheory.v_set_signature!(n, hash(Metatheory.maybe_quote_operation(x), hash(0)))
    Var{Scalar()}(roe, EGraphs.add!(roe.graph, n, false))
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

function equate!(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    (s1 == s2) || throw(SortError("Cannot equate variables of a different sort: attempted to equate $s1 with $s2"))
    v1.roe === v2.roe || error("Cannot equate variables from different graphs")
    union!(v1.roe.graph, v1.id, v2.id)
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


@nospecialize
function +(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    v1.roe === v2.roe || error("Cannot add variables from different graphs")
    s = s1 + s2
    Var{s}(v1.roe, addcall!(v1.roe.graph, +, (v1.id, v2.id)))
end

@nospecialize
+(v::Var, x::Number) = +(v, inject_number!(v.roe, x))

@nospecialize
+(x::Number, v::Var) = +(inject_number!(v.roe, x), v)

@nospecialize
function -(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    v1.roe == v2.roe || error("Cannot subtract variables from different graphs")
    s = s1 - s2
    Var{s}(v1.roe, addcall!(v1.roe.graph, -, (v1.id, v2.id)))
end

@nospecialize
-(v::Var{s}) where {s} = Var{s}(v.roe, addcall!(v.roe.graph, -, (v.id,)))

@nospecialize
-(v::Var, x::Number) = -(v, inject_number!(v.roe, x))

@nospecialize
-(x::Number, v::Var) = -(inject_number!(v.roe, x), v)

@nospecialize
function *(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    v1.roe === v2.roe || error("Cannot multiply variables from different graphs")
    s = s1 * s2
    Var{s}(v1.roe, addcall!(v1.roe.graph, *, (v1.id, v2.id)))
end

@nospecialize
*(v::Var, x::Number) = *(v, inject_number!(v.roe, x))

@nospecialize
*(x::Number, v::Var) = *(inject_number!(v.roe, x), v)

@nospecialize
function ∧(v1::Var{s1}, v2::Var{s2}) where {s1, s2}
    v1.roe === v2.roe || error("Cannot wedge variables from different graphs")
    s = s1 ∧ s2
    Var{s}(v1.roe, addcall!(v1.roe.graph, ∧, (v1.id, v2.id)))
end

@nospecialize
function ∂ₜ(v::Var{s}) where {s}
    Var{s}(v.roe, addcall!(v.roe.graph, ∂ₜ, (v.id,)))
end

@nospecialize
function d(v::Var{s}) where {s}
    s′ = d(s)
    Var{s′}(v.roe, addcall!(v.roe.graph, d, (v.id,)))
end


@nospecialize
function ★(v::Var{s}) where {s}
    s′ = ★(s)
    Var{s′}(v.roe, addcall!(v.roe.graph, ★, (v.id,)))
end

Δ(v::Var{PrimalForm(0)}) = ★(d(★(d(v))))


""" vfield :: (Decaroe -> (StateVars, ParamVars)) -> VectorFieldFunction

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
function vfield(model, operator_lookup::Dict{TypedApplication, Any})
    roe = Roe()
    (state_vars, param_vars) = model(roe)
    length(state_vars) >= 1 || error("need at least one state variable in order to create vector field")
    state_rootvars = map(state_vars) do x
        rv = extract!(x)
        rv isa RootVar || error("all state variables must be RootVars")
        rv
    end
    param_rootvars = map(param_vars) do p
        rv = extract!(p)
        rv isa RootVar || error("all param variables must be RootVars")
        rv
    end

    u = :u
    p = :p
    du = :du

    rootvar_lookup =
        Dict{RootVar, Union{Expr, Symbol}}(
            [
                [rv => :($(u)) for (i, rv) in enumerate(state_rootvars)];
                [rv => :($(p)) for (i, rv) in enumerate(param_rootvars)]
            ]
        )

    cost = derivative_cost(Set([state_rootvars; param_rootvars]))

    extractor = EGraphs.Extractor(roe.graph, cost, Float64)

    function term_select(id)
        EGraphs.find_best_node(extractor, id)
    end


    ssa = SSAExtract.SSA()

    derivative_vars = map(state_vars) do v
        SSAExtract.extract_ssa!(roe.graph, ssa, (∂ₜ(v)).id, term_select)
    end

    toexpr(v::SSAExtract.SSAVar) = Symbol("tmp%$(v.idx)")

    function toexpr(expr::SSAExtract.SSAExpr)
        if expr.fn isa RootVar
            rootvar_lookup[expr.fn]
        elseif expr.fn isa Number
            expr.fn
        else
            op = operator_lookup[TypedApplication(expr.fn, first.(expr.args))]
            if op isa Tuple
                op = op[1]
            end
            Expr(:call, *, op, toexpr.(last.(expr.args))...)
        end
    end

    ssalines = map(enumerate(ssa.statements)) do (i, expr)
        :($(toexpr(SSAExtract.SSAVar(i))) = $(toexpr(expr)))
    end

    set_derivative_stmts = map(enumerate(derivative_vars)) do (i, v)
        :($(du) .= $(toexpr(v)))
    end

    eval(
        quote
            ($du, $u, $p, _) -> begin
                $(ssalines...)
                $(set_derivative_stmts...)
            end
        end
    )
end