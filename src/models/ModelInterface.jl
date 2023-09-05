module ModelInterface

export Model, implements, @model, @instance, @withmodel

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

Models are defined in TheoryInterface because reasons
"""

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
implements(m::Module, ::Type{Val{tag}}) where {tag} = nothing

implements(m::Model, tag::ScopeTag) = implements(m, Val{tag})

implements(m::Model, theory_module::Module) =
  all(!isnothing(implements(m, gettag(scope))) for scope in theory_module.THEORY.segments.scopes)

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

"""
macro instance(head, model, body)
  # Parse the head of @instance to get theory and instance types
  (theory_module, instance_types) = @match head begin
    :($ThX{$(Ts...)}) => (ThX, Ts)
    _ => error("invalid syntax for head of @instance macro: $head")
  end


  # Get the underlying theory
  theory = macroexpand(__module__, :($theory_module.@theory))

  # A dictionary to look up the Julia type of a type constructor from its name (an ident)
  jltype_by_sort = Dict(zip(sorts(theory), instance_types)) # for type checking

  # Get the model type that we are overloading for, or nothing if this is the
  # default instance for `instance_types`
  model_type, whereparams = parse_model_param(model)
  # Parse the body into functions defined here and functions defined elsewhere
  functions, ext_functions = parse_instance_body(body)

  # Checks that all the functions are defined with the correct types Add default
  # methods for type constructors and type argument accessors if these methods
  # are missing
  typechecked_functions = typecheck_instance(theory, functions, ext_functions, jltype_by_sort)

  # Adds keyword arguments to the functions, and qualifies them by
  # `theory_module`, i.e. changes `Ob(x) = blah` to `ThCategory.Ob(x; model::M,
  # context=nothing) = blah`
  qualified_functions = 
    map(fun -> qualify_function(fun, theory_module, model_type, whereparams), typechecked_functions)

  # Declare that this model implements the theory

  implements_declarations = if !isnothing(model_type)
    map(theory.segments.scopes) do scope
      implements_declaration(model_type, scope, whereparams)
    end
  else
    []
  end

  esc(Expr(:block,
    [generate_function(f) for f in qualified_functions]...,
    implements_declarations...
  ))
end

macro instance(head, body)
  esc(:(@instance $head $(nothing) $body))
end

function parse_model_param(e)
  paramdecl, whereparams = @match e begin
    Expr(:where, paramdecl, whereparams...) => (paramdecl, whereparams)
    _ => (e, [])
  end

  model_type = @match paramdecl begin
    Expr(:tuple, Expr(:parameters, Expr(:(::), :model, model_type))) => model_type
    nothing => nothing
    _ => error("invalid syntax for declaring model type: $model")
  end

  (model_type, whereparams)
end

"""
Parses the raw julia expression into JuliaFunctions
"""
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

function default_typecon_impl(X::Ident, theory::GAT, jltype_by_sort::Dict{AlgSort})
  typecon = getvalue(theory[X])
  argtypes = [jltype_by_sort[x] for x in [AlgSort(X), sortsignature(typecon)...]]
  JuliaFunction(
    nameof(X),
    Expr0[Expr(:(::), at) for at in argtypes],
    Expr0[], Expr0[], :Bool, :(return true), nothing
  )
end

function default_accessor_impl(
  X::Ident,
  accessor::Symbol,
  jltype_by_sort::Dict{AlgSort}
)
  jltype = jltype_by_sort[AlgSort(X)]
  errormsg = "$(accessor) not defined for $(jltype)"
  JuliaFunction(
    accessor, Expr0[Expr(:(::), jltype)], Expr0[], Expr0[],
    nothing, :(error($errormsg * " in model $model"))
  )
end

function julia_signature(
  theory::GAT,
  x::Ident,
  termcon::AlgTermConstructor,
  jltype_by_sort::Dict{AlgSort}
)
  JuliaFunctionSig(
    nameof(x),
    Expr0[jltype_by_sort[sort] for sort in sortsignature(termcon)]
  )
end

function julia_signature(
  theory::GAT,
  X::Ident,
  typecon::AlgTypeConstructor,
  jltype_by_sort::Dict{AlgSort}
)
  JuliaFunctionSig(
    nameof(X),
    Expr0[jltype_by_sort[sort] for sort in [AlgSort(X), sortsignature(typecon)...]]
  )
end

function julia_signature(
  theory::GAT,
  X::Ident,
  a::Symbol,
  jltype_by_sort::Dict{AlgSort}
)
  JuliaFunctionSig(a, [jltype_by_sort[AlgSort(X)]])
end

function ExprInterop.toexpr(sig::JuliaFunctionSig)
  Expr(:call, sig.name, [Expr(:(::), type) for type in sig.types]...)
end

struct SignatureMismatchError <: Exception
  name::Symbol
  sig::Expr0
  options::Set{Expr0}
end

Base.showerror(io::IO, e::SignatureMismatchError) =
  print(io, "signature for ", e.name, ": ", e.sig,
        " does not match any of [", join(e.options, ", "), "]")

"""
Throw error if missing a term constructor. Provides default instances for type
constructors and type arguments, which return true or error, respectively.
"""
function typecheck_instance(
  theory::GAT,
  functions::Vector{JuliaFunction},
  ext_functions::Vector{Symbol},
  jltype_by_sort::Dict{AlgSort}
)::Vector{JuliaFunction}
  typechecked = JuliaFunction[]

  undefined_signatures = Dict{JuliaFunctionSig, Union{Ident, Tuple{Ident, Symbol}}}()

  overload_errormsg =
   "the types for this model declaration do not permit Julia overloading to distinguish between GAT overloads"

  for x in theory.termcons
    if nameof(x) ∉ ext_functions
      sig = julia_signature(theory, x, getvalue(theory[x]), jltype_by_sort)
      if haskey(undefined_signatures, sig)
        error(overload_errormsg)
      end
      undefined_signatures[sig] = x
    end
  end
  for X in theory.typecons
    if nameof(X) ∉ ext_functions
      sig = julia_signature(theory, X, getvalue(theory[X]), jltype_by_sort)
      if haskey(undefined_signatures, sig)
        error(overload_errormsg)
      end
      undefined_signatures[sig] = X
    end
  end
  for (a, Xs) in pairs(theory.accessors)
    if a ∉ ext_functions
      for X in Xs
        sig = julia_signature(theory, X, a, jltype_by_sort)
        if haskey(undefined_signatures, sig)
          error(overload_errormsg)
        end
        undefined_signatures[sig] = (X,a)
      end
    end
  end

  expected_signatures = DefaultDict{Symbol, Set{Expr0}}(()->Set{Expr0}())

  for (sig, n) in undefined_signatures
    name = if n isa Ident
      nameof(n)
    else
      last(n)
    end
    push!(expected_signatures[name], toexpr(sig))
  end

  for f in functions
    sig = parse_function_sig(f)

    sig ∈ keys(undefined_signatures) ||
      throw(SignatureMismatchError(f.name, toexpr(sig), expected_signatures[f.name]))

    delete!(undefined_signatures, sig)

    push!(typechecked, f)
  end

  for (_, n) in undefined_signatures
    if n isa Ident
      judgment = getvalue(theory[n])
      if judgment isa AlgTermConstructor
        error("Failed to implement $(nameof(n))")
      elseif judgment isa AlgTypeConstructor
        push!(typechecked, default_typecon_impl(n, theory, jltype_by_sort))
      end
    else
      (X, a) = n
      push!(typechecked, default_accessor_impl(X, a, jltype_by_sort))
    end
  end

  typechecked
end

"""
Add `model` kwarg (it shouldn't have it already)
Qualify method name to be in theory module
Add `context` kwargs if not already present
  
TODO: throw error if there's junk kwargs present already?
"""
function qualify_function(fun::JuliaFunction, theory_module, model_type::Union{Expr0, Nothing}, whereparams)
  kwargs = Expr0[Expr(:kw, :context, nothing)]

  (args, impl) = if !isnothing(model_type)
    m = gensym(:m)
    (
      [Expr(:(::), m, Expr(:curly, TheoryInterface.WithModel, model_type)), fun.args...],
      Expr(:let, Expr(:(=), :model, :($m.model)), fun.impl)
    )
  else
    (fun.args, fun.impl)
  end

  JuliaFunction(
    Expr(:., theory_module, QuoteNode(fun.name)),
    args,
    kwargs,
    vcat(fun.whereparams, whereparams),
    fun.return_type,
    impl,
    fun.doc
  )
end

function implements_declaration(model_type, scope, whereparams)
  notes = ImplementationNotes(nothing)
  quote
    $(GlobalRef(ModelInterface, :implements))(
      ::$(model_type), ::Type{Val{$(gettag(scope))}}
    ) where {$(whereparams...)} = $notes
  end
end

macro withmodel(model, subsexpr, body)
  modelvar = gensym("model")

  subs = @match subsexpr begin
    Expr(:tuple, subs...) => [subs...]
    sub::Symbol => [sub]
  end

  subvars = gensym.(subs) # e.g. #25compose to avoid global method overloading

  subvardefs = [
    Expr(:(=), var, sub)
    for (sub, var) in zip(subs, subvars)
  ]

  subdefs = [
    Expr(:(=), sub, :((args...;kwargs...) -> $var(args...;kwargs..., model=$modelvar)))
    for (sub, var) in zip(subs, subvars)
  ]
 
  esc(
    Expr(:let,
      Expr(:block, :($modelvar = $model), subvardefs...),
      Expr(:let,
        Expr(:block, subdefs...),
        body
      )
    )
  )
end

end
