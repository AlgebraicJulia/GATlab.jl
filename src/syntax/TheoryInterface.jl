module TheoryInterface
export @theory, Model, invoke_term

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

A constant called `THEORY` which is the `GAT` data structure.
"""

"""
When we declare a new theory, we add the scope tag of its new segment to this
dictionary pointing to the module corresponding to the new theory.
"""
const GAT_MODULE_LOOKUP = Dict{ScopeTag, Module}()

macro theory(head, body)
  (name, parentname) = @match head begin
    (name::Symbol) => (name, nothing)
    Expr(:(<:), name, parent) => (name, parent)
    _ => error("could not parse head of @theory: $head")
  end

  parent = if !isnothing(parentname)
    macroexpand(__module__, :($parentname.@theory))
  else
    GAT(:_EMPTY, GATSegment[])
  end

  newsegment = fromexpr(parent, body, GATSegment)
  importlines = Expr[]
  for line in body.args
    @switch line begin 
      @case Expr(:import, Expr(:(:), Expr(:., mod), imports)) 
        push!(importlines, line)
      @case _ 
        nothing 
    end 
  end


  theory = GAT(name, parent, newsegment)

  modulelines = Any[]

  push!(modulelines, :(export $(allnames(theory; aliases=true)...)))
  append!(modulelines, importlines)
  if !isnothing(parentname)
    push!(modulelines, Expr(:using, Expr(:(.), :(.), :(.), parentname)))
  end

  push!(modulelines, :(const THEORY = $theory))

  push!(modulelines, :(macro theory() $theory end))

  for name in Set(allnames(newsegment))
    # TODO: also push an automatically generated docstring
    push!(
      modulelines,
      quote
        function $name end

        function Base.getindex(::typeof($name), m::$(GlobalRef(TheoryInterface, :Model)))
          (args...; context=nothing) -> $name($(GlobalRef(TheoryInterface, :WithModel))(m), args...; context)
        end
      end
    )
  end

  for binding in newsegment
    bname = nameof(binding)
    judgment = getvalue(binding)
    if judgment isa Union{AlgTermConstructor, AlgTypeConstructor}
      for alias in getaliases(binding)
        if alias != bname
          push!(modulelines, :(const $alias = $bname))
        end
      end
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

function invoke_term(theory_module, types, name, args; model=nothing)
  theory = theory_module.THEORY
  method = getproperty(theory_module, name)
  type_idx = findfirst(==(name), nameof.(typecons(theory)))
  if !isnothing(type_idx) && length(args) <= 1
    args = method(types[type_idx], args...)
  elseif isnothing(model) && isempty(args)
    termcon = getvalue(theory, ident(theory; name, sig=AlgSort[]))
    idx = findfirst(==(termcon.type.head), typecons(theory))
    method(types[idx])
  elseif isnothing(model)
    method(args...)
  else
    method(WithModel(model), args...)
  end
end

end
