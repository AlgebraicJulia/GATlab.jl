module ThDEC

using ...DEC: TypedApplication, TA, Roe, RootVar 
using ...DEC.SSAExtract 

using Metatheory: VecExpr
using Metatheory.EGraphs

include("Signature.jl") # verify the signature holds 
include("EGraph.jl") # overload DEC operations to act on roe (egraphs)
include("Luke.jl") # represent operations as matrices

@nospecialize
"""    derivative_cost(allowed_roots)::Function

Returns a function `cost(n::Metatheory.VecExpr, op, costs)` which sets the cost of operations to Inf if they are either ∂ₜ or forbidden RootVars. Otherwise it computes the astsize.

"""
function derivative_cost(allowed_roots)
    function cost(n::VecExpr, op, costs)
        if op == ∂ₜ || (op isa RootVar && op ∉ allowed_roots) 
            Inf
        else
            astsize(n, op, costs)
        end
    end
end
export derivative_cost


""" vfield :: (Decaroe -> (StateVars, ParamVars)) -> VectorFieldFunction

Short for "vector field." Obtains tuple of root vars from a model, where the first component are state variables and the second are parameter variables.

Example: given a diffusivity constant a, the heat equation can be written as:
```
  ∂ₜ u = a * Δ(u)
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
function vfield(model, operator_lookup::Dict{TA, Any}=Dict{TA, Any}())
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

    ssa = SSA()

    derivative_vars = map(state_vars) do v
      extract_ssa!(roe.graph, ssa, (∂ₜ(v)).id, term_select)
    end

    toexpr(v::SSAVar) = Symbol("tmp%$(v.idx)")

    function toexpr(expr::SSAExpr)
        if expr.fn isa RootVar
            rootvar_lookup[expr.fn]
        elseif expr.fn isa Number
            expr.fn
        else
            op = operator_lookup[TypedApplication(expr.fn, first.(expr.args))]
            # Decapodes dec_* functions yield a tuple of both in-place and out-of-place function.
            # We choose the first.
            if op isa Tuple
                op = op[1]
            end
            Expr(:call, *, op, toexpr.(last.(expr.args))...)
        end
    end

    ssalines = map(enumerate(ssa.statements)) do (i, expr)
        :($(toexpr(SSAVar(i))) = $(toexpr(expr)))
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
export vfield


end
