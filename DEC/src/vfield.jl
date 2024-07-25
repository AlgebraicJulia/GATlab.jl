using .SSAs
using MLStyle

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
  we would return ([a, b],). Suppose we wanted to extract terms of the form "a + b." Since the expression "a + b" is not a RootVar, the extractor would bypass it completely.
"""
function vfield(model, op_lookup::Dict{TA, Any})

  # ::Roe
  # inttialize the Roe (e-graph)
  roe = Roe(DEC.ThDEC.Sort)

  # ::Tuple{Vector{Var}, Vector{Var}}
  # Pass the roe into the model function, which contributes the variables (via `fresh!`) and equations (via `equate!`). Retrieve the state and parameter variables in the model.
  (state_vars, param_vars) = model(roe)

  # A model is inadmissible if there is no state variables.
  length(state_vars) >= 1 || throw(VFieldError())

  # ::Vector{RootVar}
  # iterate `extract!` through the state and parameter variables.
  state_rootvars = extract_rootvars!(state_vars);
  param_rootvars = extract_rootvars!(param_vars);

  # TODO This is currently fixed 
  u = :u; p = :p; du = :du;

  # ::Dict{RootVar, Tuple{Union{Expr, Symbol}, Bool}}
  rv_lookup = make_rv_lookup(state_rootvars, param_rootvars, u, p);

  # ::Function
  # Return a cost function whose allowed roots are the set union of the model's rootvars.
  cost = derivative_cost(Set([state_rootvars; param_rootvars]))

  # ::Extractor
  # Pass the Roe's E-Graph into a Metatheory Extractor.
  extractor = EGraphs.Extractor(roe.graph, cost, Float64)

  # ::SSA
  ssa = SSA()

  # ::Function
  term_select(id) = EGraphs.find_best_node(extractor, id);

  # ::Vector{Var}
  d_vars = extract_derivative_vars!(roe, ssa, state_vars, term_select);

  # ::Tuple{Vector{Expr}, Vector{Expr}}
  # convert the SSA statements and derivative variables into Julia Exprs
  (ssalines, derivative_stmts) = build_result_body(ssa, d_vars, du, op_lookup, rv_lookup)

  # yield the function that will be passed to a solver
  eval(quote
    f(du, u, p, _) = begin
      $(ssalines...)
      $(derivative_stmts...)
    end
  end)
end
export vfield

# Build the body of the function by returning the lines of the ssas and the derivative statments.
function build_result_body(ssa, derivative_vars, du, op_lookup, rv_lookup)

  _toexpr(term) = toexpr(term, op_lookup, rv_lookup)

  ssalines = map(enumerate(ssa.statements)) do (i, stmt)
    :($(_toexpr(SSAs.Var(i))) = $(_toexpr(stmt)))
  end

  derivative_stmts = map(enumerate(derivative_vars)) do (i, stmt)
    :($(du) .= $(_toexpr(stmt)))
  end

  return (ssalines, derivative_stmts)
end

# For normalization purposes, I factored `toexpr` out of `vfield`. However, this means the two lookup variables were no longer in scope for `toexpr`. 
#
# It is possible to thread the lookups into the arguments of the `toexpr`s, 
#
# ```
#   :($(toexpr(SSAs.Var(i), lookup1, lookup2)) = $(toexpr(stmt, lookup1, lookup2)))
# ```
# but you would also need to pass the lookup arguments for the `::Var` dispatch for `toexpr`, where the variables would not be used. 
#
# Then, you could simplify this but uniting the two functions and using a conditional or @match expression. Since we are traversing a Term, we could just call the function recusively, or define one @λ.
#
# but I felt this was visually too noisy in `build_result_body`.
function toexpr(expr::Union{Term, DEC.SSAs.Var}, op_lookup, rv_lookup)
  λtoexpr = @λ begin
    var::DEC.SSAs.Var => Symbol("tmp%$(var.idx)")
    term::Term && if term.head isa Number end => term.head
    # if the head of a term is a RootVar, we'll need to ensure that we can retrieve the value from a named tuple.
    # if the boolean value is false, the rootvar is a state_var, otherwise it is a parameter and assumed to be
    # accessed by a named tuple.
    term::Term && if term.head isa RootVar end => @match rv_lookup[term.head] begin
      (rv, false) => rv
      (rv, true) => Expr(:ref, rv, term.head.name)
    end
    # This default case is Decapodes-specific. Decapode operators return a tuple of functions, so we choose the first.
    term => begin
      op = get(op_lookup, TA(term.head, first.(term.args)))
      if op isa Tuple; op = op[1] end
      Expr(:call, *, op, λtoexpr.(last.(term.args))...)
    end
  end
  λtoexpr(expr)
end

# map over the state_vars to apply `extract!`
function extract_derivative_vars!(roe::Roe, ssa::SSA, state_vars, term_select::Function)
  map(state_vars) do v
    extract!(roe.graph, ssa, (∂ₜ(v)).id, term_select)
  end
end

# given root variables, and produce a dictionary 
function make_rv_lookup(state_rvs, param_rvs, state, param)
  Dict{RootVar, Tuple{Union{Expr, Symbol}, Bool}}(
    [
      [rv => (:($(state)), false) for rv in state_rvs];
      [rv => (:($(param)), true) for rv in param_rvs]
    ]
  )
end

# map over vars
function extract_rootvars!(vars)
  map(vars) do x
    rv = extract!(x)
    rv isa RootVar ? rv : throw(RootVarError("All variables must be RootVars"))
  end
end

struct VFieldError <: Exception end

Base.showerror(io::IO, e::VFieldError) = println(io, "Need at least one state variable in order to create a vector field")

struct RootVarError <: Exception; msg::String end

Base.showerror(io::IO, e::RootVarError) = println(io, e.msg)
