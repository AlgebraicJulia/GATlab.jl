module ModelInterface

export Model, implements, @model, @instance

using ...Syntax
using ...Util.MetaUtils

using MLStyle
using DataStructures: DefaultDict


"""
`Model{Tup <: Tuple}`

A Julia value with type `Model{Tuple{Ts...}}` represents a model of some
part of the theory hierarchy, which uses the types in `Ts...` to implement
the sorts.

A model `m::Model{Tup}` is marked as implementing a `seg::GATSegmant` iff

`implements(m, ::Type{Val{gettag(seg)}}) == true`

and then we expect the following.

Let `M` be the module corresponding to `seg`.

Then for each type constructor `ty` in `seg`, we must overload

`M.ty(x, args...; model::typeof(m), context::Union{Nothing, NamedTuple})::Bool`

to return whether `x` is a valid element of `tc(args...)` with explicit context
`context` according to `m` (it is rare that you need a context for a type
constructor; notable examples include 2-cells for a bicategory).

For each argument `a` to `ty`, we must overload

`M.a(x; model::typeof(m), context::Union{Nothing, NamedTuple})`

to either error or return the argument `a` of `x`. It is perfectly
valid for this to always error, (e.g. CSetTransformations which do 
not store their domain / codomain) but it is sometimes useful and
convenient to define this, and additionally sometimes necessary for backwards
compatibility.

Finally, for each term constructor `tc` in `seg`, we must overload

`M.tc(args...; model::Typeof(m), context::Union{Nothing, NamedTuple})`

to apply the term constructor to the args. The implementation of `M.tc` should do no
validity checking; that should be assumed to have already been done. In general,
it is acceptable to error if `context` does not contain every element of the context.
However, one may in fact only need certain elements of `context`, and so it is possible
to get away without providing the context when you are writing code that is not generic
across models, and you know that, for instance, composition of FinFunctions does not
need the domains and codomains of the FinFunctions explicitly supplied.

A model `m::Model{Tup}` implements a theory iff it implements all of the GATSegments
in the theory.
"""
abstract type Model{Tup <: Tuple} end

"""
`ImplementationNotes`

Information about how a model implements a `GATSegment`. Right now, just the
docstring attached to the `@instance` macro, but could contain more info in the
future.
"""
struct ImplementationNotes
  docs::Union{String, Nothing}
end

"""
`implements(m::Model, tag::ScopeTag) -> Union{ImplementationNotes, Nothing}`

If `m` implements the GATSegment referred to by `tag`, then return the
corresponding implementation notes.
"""
implements(m::Model, tag::ScopeTag) = implements(m, Type{Val{tag}})

"""
Usage:

```julia
struct TypedFinSetC <: Model{Tuple{Vector{Int}, Vector{Int}}}
  ntypes::Int
end

@instance ThCategory{Vector{Int}, Vector{Int}} (;model::TypedFinSetC) begin
  Ob(v::Vector{Int}) = all(1 <= j <= model.ntypes for j in v)
  Hom(f::Vector{Int}, v::Vector{Int}, w::Vector{Int}) =
     length(f) == length(v) && all(1 <= y <= length(w) for y in f)

  id(v::Vector{Int}) = collect(eachindex(v))
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]

  dom(f::Vector{Int}; context) = context.dom
  codom(f::Vector{Int}; context) = context.codom
end

struct SliceCat{Ob, Hom, C <: Model{Tuple{Ob, Hom}}} <: Model{Tuple{Tuple{Ob, Hom}, Hom}}
  c::C
end

@instance ThCategory{Tuple{Ob, Hom}, Hom} (;model::SliceCat{Ob, Hom, C}) where {Ob, Hom, C<:Model{Tuple{Ob, Hom}}} begin
end
```

TODO:

- implement assuming each method is defined
- default implementations for methods
- handle aliases
- handle @import
- handle overload
"""
macro instance(head, model, body)
  (theory_module, instance_types) = @match head begin
    :($ThX{$(Ts...)}) => (ThX, Ts)
    _ => error("invalid syntax for head of @instance macro: $head")
  end

  model_type = @match model begin
    Expr(:tuple, Expr(:parameters, Expr(:(::), :model, model_type))) => model_type
    _ => error("invalid syntax for declaring model type: $model")
  end

  theory = macroexpand(__module__, :($theory_module.@theory))

  functions, ext_functions = parse_instance_body(body)

  bindings = Dict(zip(theory.typecons, instance_types)) # for type checking
  functions = typecheck_instance(theory, functions, bindings) # adds defaults too
  qualified_functions = 
    map(fun -> qualify_function(fun, theory_module, model_type), functions)

  esc(Expr(:block,
    [generate_function(f) for f in qualified_functions]...
  ))
end

"""
Throw error if missing a term constructor
Provide default instances for type constructors and type arguments, which return true or error, respectively

TODO: termcons/accessors need to be qualified by signature
"""
function typecheck_instance(theory::GAT, functions, binding)
  typechecked = JuliaFunction[]
  undefined_termcons = Set(theory.termcons)
  undefined_typecons = Set(theory.typecons)
  undefined_accessors = deepcopy(theory.accessors)
  
  inv_binding = DefaultDict{Expr0, Set{Ident}}(()->Set{Ident}()) 
  for (k,v) in pairs(binding)
    push!(inv_binding[v], k)
  end

  typecon_names = Set(nameof.(theory.typecons))
  termcon_names = Set(nameof.(theory.termcons))
  
  for f in functions
    sig = parse_function_sig(f)
    arg_types = [inv_binding[ty] for ty in sig.types] # Vector{Set{Ident}}

    if f.name ∈ keys(theory.accessors)
      # TODO: report good errors here
      f_idents = undefined_accessors[f.name]
      typecons = only(arg_types) ∩ f_idents
      typecon = only(typecons)
      delete!(undefined_accessors[f.name], typecon)
    elseif f.name ∈ typecon_names
      f_ident = ident(theory, f.name)
      typecon = getvalue(theory[f_ident])
      @assert only.(arg_types) == Ident[f_ident, [first(getvalue(binding).head) for binding in typecon.args]...]
      delete!(undefined_typecons, f_ident)
    elseif f.name ∈ termcon_names
      sig = only.(arg_types)
      f_ident = ident(theory, f.name; sig=AlgSort.(sig))
      termcon = getvalue(theory[f_ident])
      @assert sig == [first(getvalue(binding).head) for binding in termcon.args]
      delete!(undefined_termcons, f_ident)
    else 
      error("Unknown name $(f.name)")
    end
    
    push!(typechecked, f)
  end

  isempty(undefined_termcons) || error("Failed to implement $undefined_termcons")

  for utc in undefined_typecons
    typecon = getvalue(theory[utc])
    argtypes = [binding[x] for x in [utc, [first(getvalue(arg).head) for arg in typecon.args]...]]
    push!(
      typechecked, 
      JuliaFunction(nameof(utc), Expr0[Expr(:(::), at) for at in argtypes], Expr0[], :Bool, :(return true), nothing)
    )
  end

  for (uacc, typecons) in pairs(undefined_accessors)
    for typecon in typecons
      errormsg = "$(uacc) not defined for $(binding[typecon])"
      push!(
        typechecked,
        JuliaFunction(
          uacc, Expr0[Expr(:(::), binding[typecon])], Expr0[],
          nothing, :(error($errormsg * " in model $model"))
        )
      )
    end
  end

  typechecked
end

"""
Add `model` kwarg (it shouldn't have it already)
Qualify method name to be in theory module
Add `context` kwargs if not already present
  
TODO throw error if there's junk kwargs present already?
TODO: possibly add `where` clause if the model_type has a parameter
"""
function qualify_function(fun::JuliaFunction, theory_module, model_type)
  JuliaFunction(
    Expr(:., theory_module, QuoteNode(fun.name)),
    fun.args,
    Expr0[Expr(:kw, :context, nothing), Expr(:(::), :model, model_type)],
    fun.return_type,
    fun.impl,
    fun.doc
  )
end

macro instance(head, body)
  esc(:(@instance $head $(nothing) $body))
end

function parse_instance_body(expr::Expr)
  @assert expr.head == :block
  funs = JuliaFunction[]
  ext_funs = Symbol[]
  for elem in strip_lines(expr).args
    elem = strip_lines(elem)
    head = elem.head
    if head == :macrocall && elem.args[1] == Symbol("@import")
      ext_funs = @match elem.args[2] begin
        sym::Symbol => [ext_funs; [sym]]
        Expr(:tuple, args...) => [ext_funs; Symbol[args...]]
      end
    else
      push!(funs, parse_function(elem))
    end
  end
  return (funs, ext_funs)
end

end
