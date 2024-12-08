module TheoryInterface
export @theory, @signature, Model, invoke_term

using ..Scopes, ..GATs, ..ExprInterop, GATlab.Util
# using GATlab.Util

using MLStyle, StructEquality, Markdown

abstract type Model{Tup <: Tuple} end

@struct_hash_equal struct WithModel{M <: Model}
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

# TODO is every contribution to a theory a new segment, or can a new theory introduce multiple segments? 
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

"""
Fully Qualified Module Name
"""
function fqmn(mod::Module)
  names = Symbol[]
  while parentmodule(mod) != mod
    push!(names, nameof(mod))
    mod = parentmodule(mod)
  end
  push!(names, nameof(mod))
  reverse(names)
end


function usetheory!(host::GAT, guest::GAT)
  for segment in guest.segments.scopes
    if !hastag(host, gettag(segment))
      GATs.unsafe_pushsegment!(host, segment)
    end
  end
end

"""
Accepts a name, a theory body and returns a theory
"""
function expand_theory(parentname, body, __module__)
  theory = if !isnothing(parentname)
    copy(macroexpand(__module__, :($parentname.Meta.@theory)))
  else
    GAT(:_EMPTY)
  end

  usings = []

  # collect renames
  for line in body.args
    @match line begin
      Expr(:using, Expr(:(.), other)) => begin
        othertheory = macroexpand(__module__, :($other.Meta.@theory))
        push!(usings, :(using ..$other))
        usetheory!(theory, othertheory)
      end
      _ => nothing
    end
  end

  (theory, usings)
end

function theory_impl(head, body, __module__)
  (name, parentname) = @match head begin
    (name::Symbol) => (name, nothing)
    Expr(:(<:), name, parent) => (name, parent) # TODO make parents
    _ => error("could not parse head of @theory: $head")
  end

  (parent, usings) = expand_theory(parentname, body, __module__)

  theory = fromexpr(parent, body, GAT; name, current_module=fqmn(__module__))

  newsegment = theory.segments.scopes[end]
  docstr = repr(theory)

  lines = Any[]
  newnames = Symbol[]
  structlines = Expr[]
  structnames = Set([nameof(s.declaration) for s in structs(theory)])
  for scope in theory.segments.scopes
    if !hastag(parent, gettag(scope))
      for binding in scope # XXX newsegment
        judgment = getvalue(binding)
        bname = nameof(binding)
        if judgment isa Union{AlgDeclaration, Alias} && bname ∉ structnames
          push!(lines, juliadeclaration(bname))
          push!(newnames, bname)
        elseif judgment isa AlgStruct
          push!(structlines, mk_struct(judgment, fqmn(__module__)))
        end
      end
    end
  end

  modulelines = Any[]

  append!(modulelines, usings)
  # this exports the names of the module, e.g. :default, :⋅, :e 
  push!(modulelines, :(export $(allnames(theory; aliases=true)...)))

  push!(
    modulelines,
    Expr(:using,
      Expr(:(:),
        Expr(:(.), :(.), :(.), nameof(__module__)),
        Expr.(Ref(:(.)), newnames)...
      )
    )
  )

  # TODO deprecated?
  if !isnothing(parentname)
    push!(modulelines, Expr(:using, Expr(:(.), :(.), :(.), parentname)))
  end
  
  doctarget = gensym()
  mdp(::Nothing) = []
  mdp(x::Base.Docs.DocStr) = Markdown.parse(x.text...)

  push!(modulelines, Expr(:toplevel, :(module Meta
    struct T end
   
    const theory = $theory

    macro theory() $theory end
    macro theory_module() parentmodule(@__MODULE__) end
  end)))

  # XXX
  push!(modulelines, :($(GlobalRef(TheoryInterface, :GAT_MODULE_LOOKUP))[$(gettag(newsegment))] = $name))


  esc(
    Expr(
      :toplevel,
      lines...,
      :(const $(doctarget) = nothing),
      :(Core.@__doc__ $(doctarget)),
      :(
        module $name
        $(modulelines...)
        $(structlines...)
        end
      ),
      :(@doc ($(Markdown.MD)($mdp(@doc $doctarget), $docstr)) $name)
    )
  )
end

function juliadeclaration(name::Symbol)
  quote
    function $name end

    if Base.isempty(Base.methods(Base.getindex, [typeof($name), $(GlobalRef(TheoryInterface, :Model))]))
      function Base.getindex(::typeof($name), m::$(GlobalRef(TheoryInterface, :Model)))
        (args...; context=nothing) -> $name($(GlobalRef(TheoryInterface, :WithModel))(m), args...; context)
      end
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


"""

"""
function mk_struct(s::AlgStruct, mod)
  fields = map(argsof(s)) do b
    Expr(:(::), nameof(b), nameof(AlgSort(getvalue(b))))
  end 
  sorts = unique([f.args[2] for f in fields])
  she = Expr(:macrocall, GlobalRef(StructEquality, Symbol("@struct_hash_equal")), mod, nameof(s))
  quote
    struct $(nameof(s)){$(sorts...)}
      $(fields...)
    end

    $she
  end
end

end
