module ModelInterface

using ...Syntax
using ...Util.MetaUtils

export Model, implements, @model

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

`M.ty(x, args...; model::typeof(m), context::Union{Nothing, NamedTuple})::Boolean`

to return whether `x` is a valid element of `tc(args...)` with explicit context
`context` according to `m` (it is rare that you need a context for a type
constructor; notable examples include 2-cells for a bicategory).

For each argument `a` to `ty`, we must overload

`M.a(x; model::typeof(m), args::Union{Nothing, NamedTuple}, context::Union{Nothing, NamedTuple})`

to return either `nothing` or the type argument `a` of `x`. It is perfectly
valid for this to always return `nothing`, but it is sometimes useful and
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
implements(m::Model, tag::ScopeTag) = implements(m, ::Type{Val{tag}})

"""
Usage:

```julia
struct TypedFinSetC <: Model{Tuple{Vector{Int}, Vector{Int}}}
  ntypes::Int
end

@instance Category{Vector{Int}, Vector{Int}} (;model::TypedFinSetC) begin
  Ob(v::Vector{Int}) = all(1 <= j <= model.ntypes for j in v)
  Hom(f::Vector{Int}, v::Vector{Int}, w::Vector{Int}) =
     length(f) == length(v) && all(1 <= y <= length(w) for y in f)

  id(v::Vector{Int}) = collect(eachindex(v))
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]

  dom(f::Vector{Int}; args) = args.dom
  codom(f::Vector{Int}; args) = args.codom
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

  theory = macroexpand(__module__, :($theory_module.@theory))

  functions, ext_functions = parse_instance_body(body)

  bindings = Dict(zip(theory.typecons, instance_types))
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
