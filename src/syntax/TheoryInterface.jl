module TheoryInterface
export @theory, @signature, Model, invoke_term

using ..Scopes, ..GATs, ..ExprInterop

using MLStyle

abstract type Model{Tup <: Tuple} end

struct WithModel{M <: Model}
  model::M
end

"""
Each theory corresponds to a module, which has the following items.

For each new term constructor in the theory, a newly declared function with the
name of that term constructor.

For each new type constructor in the theory, a newly declared function with the
name of that type constructor.

For each type parameter to a new type constructor in the theory, a function with
the name of that type parameter.

For all of the old term constructors/type constructors/type parameters, imports
from the modules that define them.

For all aliases, `const` declarations that make them equal to their primaries.

A macro called `@theory` which expands to the `GAT` data structure for the module.

A constant called `Meta.theory` which is the `GAT` data structure.
"""

"""
When we declare a new theory, we add the scope tag of its new segment to this
dictionary pointing to the module corresponding to the new theory.
"""
const GAT_MODULE_LOOKUP = Dict{ScopeTag, Module}()

macro signature(head, body)
  theory_impl(head, body, __module__)
end

macro theory(head, body)
  theory_impl(head, body, __module__)
end

function theory_impl(head, body, __module__)
  (name, parentname) = @match head begin
    (name::Symbol) => (name, nothing)
    Expr(:(<:), name, parent) => (name, parent)
    _ => error("could not parse head of @theory: $head")
  end

  parent = if !isnothing(parentname)
    macroexpand(__module__, :($parentname.Meta.@theory))
  else
    GAT(:_EMPTY)
  end

  theory = fromexpr(parent, body, GAT; name)
  newsegment = theory.segments.scopes[end]

  modulelines = Any[]

  push!(modulelines, :(export $(allnames(theory; aliases=true)...)))

  for x in keys(theory.resolvers)
    decl = getvalue(theory[x])
    if !isnothing(decl.overloads)
      push!(
        modulelines,
        Expr(:import,
          Expr(:(:), Expr(:(.), decl.overloads[1:end-1]...), Expr(:(.), decl.overloads[end]))
        )
      )
    end
  end

  if !isnothing(parentname)
    push!(modulelines, Expr(:using, Expr(:(.), :(.), :(.), parentname)))
  end

  push!(modulelines, Expr(:toplevel, :(module Meta
    struct T end
    const theory = $theory
    macro theory() $theory end
    macro theory_module() parentmodule(@__MODULE__) end
  end)))

  for binding in newsegment
    judgment = getvalue(binding)
    bname = nameof(binding)
    if judgment isa AlgDeclaration
      push!(modulelines, juliadeclaration(bname, judgment))
    elseif judgment isa Alias
      push!(modulelines, :(const $bname = $(nameof(judgment.ref))))
    end
  end

  push!(modulelines, :($(GlobalRef(TheoryInterface, :GAT_MODULE_LOOKUP))[$(gettag(newsegment))] = $name))

  esc(
    Expr(
      :toplevel,
      :(
        module $name
        $(modulelines...)
        end
      ),
      :(Core.@__doc__ $(name))
    )
  )
end

function juliadeclaration(name::Symbol, judgment::AlgDeclaration)
  decl = if isnothing(judgment.overloads)
    :(function $name end)
  else
    Expr(:import,
      Expr(
        :(:),
        Expr(:(.), judgment.overloads[1:end-1]...),
        Expr(:as, Expr(:(.), judgment.overloads[end]), name)
      )
    )
  end
  quote
    $decl

    function Base.getindex(::typeof($name), m::$(GlobalRef(TheoryInterface, :Model)))
      (args...; context=nothing) -> $name($(GlobalRef(TheoryInterface, :WithModel))(m), args...; context)
    end
  end
end

function invoke_term(theory_module, types, name, args; model=nothing)
  theory = theory_module.Meta.theory
  method = getproperty(theory_module, name)
  type_idx = findfirst(==(name), nameof.(sorts(theory)))
  if !isnothing(type_idx) && length(args) <= 1
    args = method(types[type_idx], args...)
  elseif isnothing(model) && isempty(args)
    x = ident(theory; name)
    method_id = resolvemethod(theory.resolvers[x], AlgSort[])
    termcon = getvalue(theory[method_id])
    idx = findfirst(==(AlgSort(termcon.type)), sorts(theory))
    method(types[idx])
  elseif isnothing(model)
    method(args...)
  else
    method(WithModel(model), args...)
  end
end

end
