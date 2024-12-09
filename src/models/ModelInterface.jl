
"""
Any Julia struct can be a model of a GAT. A model is marked as implementing a 
`seg::GATSegment` iff

`implements(m, ::Type{Val{gettag(seg)}}) == true`

and then we expect the following.

Let `M` be the module corresponding to `seg`.

Then for each type constructor `ty` in `seg`, we must overload

`M.ty(wm::WithModel{typeof(m)}, x, args...; context::Union{Nothing, NamedTuple})::Bool`

to attempt to coerce `x` to a valid element of `tc(args...)` with explicit context
`context` according to `m` (it is rare that you need a context for a type
constructor; notable examples include 2-cells for a bicategory).

For each argument `a` to `ty`, we must overload

`M.a(wm::WithModel{typeof(m)}, x;, context::Union{Nothing, NamedTuple})`

to either error or return the argument `a` of `x`. It is perfectly
valid for this to always error, (e.g. CSetTransformations which do 
not store their domain / codomain) but it is sometimes useful and
convenient to define this, and additionally sometimes necessary for backwards
compatibility.

Finally, for each term constructor `tc` in `seg`, we must overload

`M.tc(wm::WithModel{typeof(m)}, args...; context::Union{Nothing, NamedTuple})`

to apply the term constructor to the args. The implementation of `M.tc` should do no
validity checking; that should be assumed to have already been done. In general,
it is acceptable to error if `context` does not contain every element of the context.
However, one may in fact only need certain elements of `context`, and so it is possible
to get away without providing the context when you are writing code that is not generic
across models, and you know that, for instance, composition of FinFunctions does not
need the domains and codomains of the FinFunctions explicitly supplied.

A model implements a theory iff it implements all of the GATSegments
in the theory.
"""
module ModelInterface

export implements, impl_type, TypeCheckFail, SignatureMismatchError, 
       @model, @instance, @withmodel, @fail, migrate_model

using ...Syntax
using ...Util.MetaUtils
using ...Util.MetaUtils: JuliaFunctionSigNoWhere

import ...Syntax.TheoryMaps: migrator 
using ...Syntax.TheoryMaps: dom, codom
using ...Syntax.TheoryInterface: GAT_MODULE_LOOKUP

using MLStyle
using DataStructures: DefaultDict, OrderedDict


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
`implements(m::MyModel, tag::ScopeTag) -> Union{ImplementationNotes, Nothing}`

If `m` implements the GATSegment referred to by `tag`, then return the
corresponding implementation notes.
"""
implements(m, ::Type{Val{tag}}) where {tag} = nothing

implements(m, tag::ScopeTag) = implements(m, Val{tag})

impl_type(m, tag::ScopeTag) = impl_type(m, Val{tag})

impl_type(m, mod::Module, name::Symbol) = 
  impl_type(m, gettag(ident(mod.Meta.theory; name)))


implements(m, theory_module::Module) =
  all(!isnothing(implements(m, gettag(scope))) for scope in theory_module.Meta.theory.segments.scopes)

struct TypeCheckFail <: Exception
  model::Any
  theory::GAT
  type::Ident
  val::Any
  args::AbstractVector
  reason::Any
end

function Base.showerror(io::IO, err::TypeCheckFail)
  println(io, "TypeCheckFail:")
  print(io, "$(err.val) is not a valid $(err.type)(")
  join(io, err.args, ", ")
  println(io, ") in model $(err.model) of theory $(nameof(err.theory)) because:")
  println(io, err.reason)
end

"""
Usage:

```julia
struct TypedFinSetC
  ntypes::Int
end

@instance ThCategory{Vector{Int}, Vector{Int}} [model::TypedFinSetC] begin
  Ob(v::Vector{Int}) = all(1 <= j <= model.ntypes for j in v)
  Hom(f::Vector{Int}, v::Vector{Int}, w::Vector{Int}) =
     length(f) == length(v) && all(1 <= y <= length(w) for y in f)

  id(v::Vector{Int}) = collect(eachindex(v))
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]

  dom(f::Vector{Int}; context) = context.dom
  codom(f::Vector{Int}; context) = context.codom
end

struct SliceC{ObT, HomT, C}
  cat::C
  over::ObT
  function SliceC(cat::C, over) where C
    implements(cat, ThCategory) || error("Bad cat $cat")
    obtype = impl_type(cat, ThCategory, :Ob)
    homtype = impl_type(cat, ThCategory, :Hom)
    new{obtype, homtype, C}(cat, ThCategory.Ob[cat](over))
  end
end

@instance ThCategory{Tuple{Ob, Hom}, Hom} [model::SliceCat{Ob, Hom, C}] where {Ob, Hom, C}}} begin
end
```

"""
macro instance(head, model, body)
  # Parse the head of @instance to get theory and instance types
  # TODO: should we allow instance types to be nothing? Is this in Catlab?
  (theory_module, instance_types) = @match head begin
    :($ThX{$(Ts...)}) => (ThX, Ts)
    _ => error("invalid syntax for head of @instance macro: $head")
  end

  # Get the underlying theory
  theory = macroexpand(__module__, :($theory_module.Meta.@theory))

  # A dictionary to look up the Julia type of a type constructor from its name (an ident)
  jltype_by_sort = Dict{AlgSort,Expr0}([
    zip(primitive_sorts(theory), instance_types)..., 
    [s => nameof(headof(s)) for s in struct_sorts(theory)]...
  ]) 

  # Get the model type that we are overloading for, or nothing if this is the
  # default instance for `instance_types`
  model_type, whereparams = parse_model_param(model)


  # Create the actual instance
  generate_instance(theory, theory_module, jltype_by_sort, model_type, whereparams, body)
end

function generate_instance(
  theory::GAT,
  theory_module::Union{Expr0, Module},
  jltype_by_sort::Dict{AlgSort},
  model_type::Union{Expr0, Nothing},
  whereparams::AbstractVector,
  body::Expr;
  typecheck=true,
  escape=true
)
  # The old (Catlab) style of instance, where there is no explicit model
  oldinstance = isnothing(model_type)

  # Parse the body into functions defined here and functions defined elsewhere
  functions, ext_functions = parse_instance_body(body, theory)

  # Checks that all the functions are defined with the correct types. Adds default
  # methods for type constructors and type argument accessors if these methods
  # are missing
  typechecked_functions = if typecheck
    typecheck_instance(theory, functions, ext_functions, jltype_by_sort; oldinstance, theory_module)
  else
    [functions..., ext_functions...] # skip typechecking and expand_fail
  end

  # Adds keyword arguments to the functions, and qualifies them by
  # `theory_module`, i.e. changes
  # `Ob(x) = blah`
  # to
  # `ThCategory.Ob(m::WithModel{M}, x; context=nothing) = let model = m.model in blah end`
  qualified_functions =
    map(fun -> qualify_function(fun, theory_module, model_type, whereparams, 
                                Set(nameof.(structs(theory)))), 
        typechecked_functions)

  append!(
    qualified_functions,
    make_alias_definitions(theory, theory_module, jltype_by_sort, model_type, 
                           whereparams, ext_functions)
  )

  # Declare that this model implements the theory

  implements_declarations = if !isnothing(model_type)
    map(theory.segments.scopes) do scope
      implements_declaration(model_type, scope, whereparams)
    end
  else
    []
  end

  impl_type_declarations = if isnothing(model_type) 
    Expr[]
  else 
    map(collect(jltype_by_sort)) do (k, v)
      impl_type_declaration(model_type, whereparams, k, v)
    end
  end
  docsink = gensym(:docsink)

  code = Expr(:block,
    [generate_function(f) for f in qualified_functions]...,
    impl_type_declarations...,
    implements_declarations...,
    :(function $docsink end),
    :(Core.@__doc__ $docsink)
  )

  escape ? esc(code) : code
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
    Expr(:vect, Expr(:(::), :model, model_type)) => model_type
    nothing => nothing
    _ => error("invalid syntax for declaring model type: $paramdecl")
  end

  (model_type, whereparams)
end

"""
Parses the raw julia expression into JuliaFunctions
"""
function parse_instance_body(expr::Expr, theory::GAT)
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
      fun = parse_function(elem)
      fun = setname(fun, nameof(ident(theory; name=fun.name)))
      push!(funs, fun)
    end
  end
  return (funs, ext_funs)
end

function args_from_sorts(sorts::AlgSorts, jltype_by_sort::Dict{AlgSort})
  Expr0[Expr(:(::), gensym(), jltype_by_sort[s]) for s in sorts]
end

function default_typecon_impl(X::Ident, theory::GAT, jltype_by_sort::Dict{AlgSort})
  typecon = getvalue(theory[X])
  sort = AlgSort(getdecl(typecon), X)
  jltype = jltype_by_sort[sort]
  args = args_from_sorts([sort; sortsignature(typecon)], jltype_by_sort)
  JuliaFunction(
    name = nameof(getdecl(typecon)),
    args = args,
    return_type = jltype,
    impl = :(return $(args[1].args[1])),
  )
end

function default_accessor_impl(x::Ident, theory::GAT, jltype_by_sort::Dict{AlgSort})
  acc = getvalue(theory[x])
  sort = AlgSort(acc.typecondecl, acc.typecon)
  jltype = jltype_by_sort[sort]
  errormsg = "$(acc) not defined for $(jltype)"
  JuliaFunction(;
    name = nameof(getdecl(acc)),
    args = Expr0[Expr(:(::), jltype)],
    impl = :(error($errormsg * " in model $model"))
  )
end

julia_signature(theory::GAT, x::Ident, jltype_by_sort::Dict{AlgSort}) = 
  julia_signature(getvalue(theory[x]), jltype_by_sort; X=x)

function julia_signature(
  termcon::AlgTermConstructor,
  jltype_by_sort::Dict{AlgSort};
  oldinstance=false, kw...
)
  sortsig = sortsignature(termcon)
  args = if oldinstance && isempty(sortsig)
    Expr0[Expr(:curly, :Type, jltype_by_sort[AlgSort(termcon.type)])]
  else
    Expr0[jltype_by_sort[sort] for sort in sortsig if !GATs.iseq(sort)]
  end
  JuliaFunctionSig(
    nameof(getdecl(termcon)),
    args
  )
end

function julia_signature(
  typecon::AlgTypeConstructor,
  jltype_by_sort::Dict{AlgSort};
  X, kw...
)
  decl = getdecl(typecon)
  sort = AlgSort(decl, X)
  JuliaFunctionSig(
    nameof(decl),
    Expr0[jltype_by_sort[sort] for sort in [sort, sortsignature(typecon)...]]
  )
end

function julia_signature(
  acc::AlgAccessor,
  jltype_by_sort::Dict{AlgSort};
  kw...
)
  jlargtype = jltype_by_sort[AlgSort(acc.typecondecl, acc.typecon)]
  JuliaFunctionSig(nameof(getdecl(acc)), [jlargtype])
end


function julia_signature(str::AlgFunction, jltype_by_sort::Dict{AlgSort}; kw...)
  sortsig = sortsignature(str)
  args = Expr0[jltype_by_sort[sort] for sort in sortsig]
  JuliaFunctionSig(
    nameof(getdecl(str)),
    args
  )
end

function ExprInterop.toexpr(sig::JuliaFunctionSig)
  Expr(:call, sig.name, [Expr(:(::), type) for type in sig.types]...)
end
ExprInterop.toexpr(sig::JuliaFunctionSigNoWhere) = 
  ExprInterop.toexpr(sig |> JuliaFunctionSig)

struct SignatureMismatchError <: Exception
  name::Symbol
  sig::Expr0
  options::Set{Expr0}
end

Base.showerror(io::IO, e::SignatureMismatchError) =
  print(io, "signature for ", e.name, ": ", e.sig,
        " does not match any of [", join(e.options, ", "), "]")

const fail_var = gensym(:fail)

macro fail(str)
  esc(Expr(:call, fail_var, str))
end

"""
Throw error if missing a term constructor. Provides default instances for type
constructors and type arguments, which return true or error, respectively.
"""
function typecheck_instance(
  theory::GAT,
  functions::Vector{JuliaFunction},
  ext_functions::Vector{Symbol},
  jltype_by_sort::Dict{AlgSort};
  oldinstance=false,
  theory_module=nothing,
)::Vector{JuliaFunction}
  typechecked = JuliaFunction[]

  # The overloads that we have to provide
  undefined_signatures = Dict{JuliaFunctionSigNoWhere, Tuple{Ident, Ident}}()

  overload_errormsg =
   "the types for this model declaration do not permit Julia overloading to distinguish between GAT overloads"
  for (decl, resolver) in theory.resolvers
    for (_, x) in allmethods(resolver)
      if getvalue(theory[x]) isa AlgStruct 
        continue 
      end
      sig = julia_signature(getvalue(theory[x]), jltype_by_sort; oldinstance, X=x) |> JuliaFunctionSigNoWhere
      if haskey(undefined_signatures, sig)
        error(overload_errormsg * ": $x vs $(undefined_signatures[sig])")
      end
      undefined_signatures[sig] = (decl, x)
    end
  end

  for x in getidents(theory)
    v = getvalue(theory[x])
    if v isa AlgFunction 
      push!(typechecked, mk_fun(v, theory, theory_module, jltype_by_sort))
    end 
  end

  expected_signatures = DefaultDict{Ident, Set{Expr0}}(()->Set{Expr0}())

  for (sig, (decl, _)) in undefined_signatures
    push!(expected_signatures[decl], toexpr(sig))
  end

  for f in functions
    sig = parse_function_sig(f) |> JuliaFunctionSigNoWhere
    if haskey(undefined_signatures, sig)
      (decl, method) = undefined_signatures[sig]

      judgment = getvalue(theory, method)

      if judgment isa AlgTypeConstructor
        f = expand_fail(theory, decl, f) 
      end

      delete!(undefined_signatures, sig)

      push!(typechecked, f)
    else
      if hasname(theory, f.name)
        x = ident(theory; name=f.name)
        throw(SignatureMismatchError(f.name, toexpr(sig), expected_signatures[x]))
      else
        error("no declaration in the theory has name $f.name")
      end
      # TODO: allow extra overloads for type constructors to provide additional coercions
      # try
      #   x = ident(theory; name=f.name)
      # catch e
      #   throw(SignatureMismatchError(f.name, toexpr(sig), expected_signatures[f.name]))
      # end

      # methods = last.(allmethods(theory.resolvers[x]))

      # if !(any(getvalue(theory[m]) isa AlgTypeConstructor for m in methods))
      # end

      # push!(typechecked, expand_fail(theory, x, f))
    end
  end

  for (sig, (decl, method)) in undefined_signatures
    nameof(decl) ∈ ext_functions && continue # assume it has been impl'd already
    judgment = getvalue(theory[method])
    if judgment isa AlgTermConstructor
      error("Failed to implement $decl: $(toexpr(sig))")
    elseif judgment isa AlgTypeConstructor
      push!(typechecked, default_typecon_impl(method, theory, jltype_by_sort))
    elseif judgment isa AlgAccessor
      push!(typechecked, default_accessor_impl(method, theory, jltype_by_sort))
    end
  end

  typechecked
end

function expand_fail(theory::GAT, x::Ident, f::JuliaFunction)
  argname(arg::Expr) = first(arg.args)
  setimpl(
    f,
    quote
      let $(fail_var) =
        reason -> throw(
          $(TypeCheckFail)(
            model,
            $theory,
            $x,
            $(argname(f.args[1])),
            $(Expr(:vect, argname.(f.args[2:end])...)),
            reason
          ))
        $(f.impl)
      end
    end
  )
end

function mk_fun(f::AlgFunction, theory, mod, jltype_by_sort)
  name = nameof(f.declaration)
  args = map(zip(f.args, sortsignature(f))) do (i,s)
    Expr(:(::),nameof(f[i]),jltype_by_sort[s])
  end
  argnames = Vector{Symbol}(undef, length(getcontext(f)))
  setindex!.(Ref(argnames), [nameof(f[i]) for i in f.args], getvalue.(f.args))
  impl = to_call_impl(f.value,theory, mod, argnames, false)
  JuliaFunction(;name=name, args, impl)
end

function make_alias_definitions(theory, theory_module, jltype_by_sort, model_type, whereparams, ext_functions)
  lines = []
  oldinstance = isnothing(model_type)
  for segment in theory.segments.scopes
    for binding in segment
      alias = getvalue(binding)
      name = nameof(binding)
      if alias isa Alias && name ∉ ext_functions
        for (argsorts, method) in allmethods(theory.resolvers[alias.ref])
          args = [(gensym(), jltype_by_sort[sort]) for sort in argsorts]
          args = if oldinstance
            if length(args) == 0
              termcon = getvalue(theory[method])
              retsort = AlgSort(termcon.type)
              [(gensym(), Expr(:curly, Type, jltype_by_sort[retsort]))]
            else
              args
            end
          else
            [(gensym(:m), :($(TheoryInterface.WithModel){<:$model_type})); args]
          end
          argexprs = [Expr(:(::), p...) for p in args]
          overload = JuliaFunction(;
            name = :($theory_module.$name),
            args = argexprs,
            kwargs = [Expr(:(...), :kwargs)],
            whereparams,
            impl = :($theory_module.$(nameof(alias.ref))($(first.(args)...); kwargs...))
          )
          push!(lines, overload)
        end
      end
    end
  end
  lines
end

"""
Add `WithModel` param first, if this is not an old instance (it shouldn't have it already)
Qualify method name to be in theory module
Qualify args to struct types
Add `context` kwargs if not already present
"""
function qualify_function(fun::JuliaFunction, theory_module, model_type::Union{Expr0, Nothing}, whereparams, structnames)
  kwargs = filter(fun.kwargs) do kwarg
    @match kwarg begin
      Expr(:kw, :context, _) => false
      :context => false
      Expr(:(::), :context, _) => false
      Expr(:kw, Expr(:(::), :context, _), _) => false
      _ => true
    end
  end
  kwargs = Expr0[Expr(:kw, :context, nothing); kwargs]
  (args, impl) = if !isnothing(model_type)
    args = map(fun.args) do arg
      @match arg begin
        Expr(:(::), argname, ty) => Expr(:(::), argname,
          ty ∈ structnames ? Expr(:., theory_module, QuoteNode(ty)) : ty )
        _ => arg
      end
    end

    m = gensym(:m)
    (
      [Expr(:(::), m, Expr(:curly, TheoryInterface.WithModel, Expr(:<:, model_type))), args...],
      Expr(:let, Expr(:(=), :model, :($m.model)), fun.impl)
    )
  else
    (fun.args, Expr(:let, Expr(:(=), :model, nothing), fun.impl))
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

function impl_type_declaration(model_type, whereparams, sort, jltype)
  quote 
    if !hasmethod($(GlobalRef(ModelInterface, :impl_type)), 
      ($(model_type) where {$(whereparams...)}, Type{Val{$(gettag(getdecl(sort)))}}))
      $(GlobalRef(ModelInterface, :impl_type))(
          ::$(model_type), ::Type{Val{$(gettag(getdecl(sort)))}}
        ) where {$(whereparams...)} = $(jltype)
    end
  end
end

function implements_declaration(model_type, scope, whereparams)
  notes = ImplementationNotes(nothing)
  m = only(methods(implements, (Any, Type{Val{1}})))
  quote
    if $m == only(methods($(GlobalRef(ModelInterface, :implements)), 
        ($(model_type) where {$(whereparams...)}, Type{Val{$(gettag(scope))}})))
      $(GlobalRef(ModelInterface, :implements))(
        ::$(model_type), ::Type{Val{$(gettag(scope))}}
      ) where {$(whereparams...)} = $notes
    end
  end
end


macro withmodel(model, subsexpr, body)
  modelvar = gensym("model")

  # e.g., (ℕ, Z, S) => [ℕ, Z, S]
  subs = @match subsexpr begin
    Expr(:tuple, subs...) => [subs...]
    sub::Symbol => [sub]
  end

  # gensym these subs
  subvars = gensym.(subs) # e.g. #25compose to avoid global method overloading

  # set gensym(ℕ) = ℕ, etc.
  subvardefs = [
    Expr(:(=), var, sub)
    for (sub, var) in zip(subs, subvars)
  ]

  # set ℕ = (args...; kwargs...) -> gensym(ℕ)(MyModel, args...; kwargs...) 
  subdefs = [
    Expr(:(=), sub, :((args...;kwargs...) -> $var($modelvar, args...;kwargs...)))
    for (sub, var) in zip(subs, subvars)
  ] 

  esc(
    Expr(:let,
      Expr(:block, :($modelvar = $(Expr(:call, TheoryInterface.WithModel, model))), subvardefs...),
      Expr(:let,
        Expr(:block, subdefs...),
        body
      )
    )
  )
end

# Until GAT_MODULE_LOOKUP is debugged, we can only migrate with the Module
# migrate_model(F::Module, m::Any, new_model_name=nothing) = 
#   migrate_model(F.MAP, m, new_model_name)

"""
Given a theory map A -> B, construct a new struct type which wraps a model of
theory B and is itself a model of theory A. The name of the struct can be
optionally given, otherwise it is gensym'd. The resulting expression is an
instance of that struct type.

Future work: There is some subtlety in how accessor functions should be handled.
TODO: The new instance methods do not yet handle the `context` keyword argument.
"""
function migrate_model(FM::Module, m::Any, new_model_name::Union{Nothing,Symbol}=nothing)
  new_model_name = isnothing(new_model_name) ? gensym(:Migrated) : new_model_name
  F = FM.MAP
  dom_module =  macroexpand(FM, :($FM.@dom)) #GAT_MODULE_LOOKUP[gettag(dom_theory)]
  codom_module = macroexpand(FM, :($FM.@codom)) #GAT_MODULE_LOOKUP[gettag(codom_theory)]
  dom_theory = dom_module.Meta.theory #dom(F)
  codom_theory = codom_module.Meta.theory #codom(F)

  # Expressions which evaluate to the correct Julia type
  jltype_by_sort = Dict(map(sorts(dom_theory)) do v
    v => :(impl_type($m, gettag(getdecl(AlgSort($F($v.method).val)))))
  end)

  _x = gensym("val")

  accessor_funs = JuliaFunction[] # added to during typecon_funs loop

  typecon_funs = map(collect(typemap(F))) do (x, fx)
    typecon = getvalue(dom_theory[x])

    # Accessors
    #----------
    # accessor arg is a value of the type constructor's result type
    args = [:($_x::$(jltype_by_sort[AlgSort(typecon.declaration, x)]))]
    # Equations are how the value of the accessor is related to the type 
    eq = equations(codom_theory, fx)
    scopedict = Dict(gettag(typecon.localcontext) => gettag(fx.ctx))
    accessors = idents(typecon.localcontext; lid=typecon.args)
    for accessor in retag.(Ref(scopedict), accessors)
      name = nameof(accessor)
      # If we have a means of computing the accessor...
      if !isempty(eq[accessor])
        rtype = typecon.localcontext[ident(typecon.localcontext; name)]
        return_type = jltype_by_sort[AlgSort(getvalue(rtype))]
        # Convert accessor expression into Julia expression
        impl = to_call_accessor(first(eq[accessor]), _x, codom_module)
        push!(accessor_funs, JuliaFunction(;name, args, return_type, impl))
      end
    end

    # Type constructor function
    #--------------------------
    codom_body = bodyof(fx.val) 
    fxname = nameof(headof(codom_body))
    sig = julia_signature(dom_theory, x, jltype_by_sort)
    
    name = nameof(typecon.declaration)

    argnames = [_x, nameof.(argsof(typecon))...]
    args = [:($k::$(v)) for (k, v) in zip(argnames, sig.types)]
    
    return_type = first(sig.types)
    argnames′ = Array{Symbol}(undef, length(getcontext(typecon)))
    setindex!.(Ref(argnames′), argnames[2:end], getvalue.(typecon.args))

    impls = to_call_impl.(codom_body.args, Ref(codom_theory), Ref(codom_module), 
                          Ref(argnames′), true)
    impl = Expr(:call, Expr(:ref, :($codom_module.$fxname), 
                            :(model.model)), _x, impls...)
    JuliaFunction(;name, args, return_type, impl)
  end


  termcon_funs = map(collect(termmap(F))) do (x, fx)
    termcon = getvalue(dom_theory[x])
    sig = julia_signature(dom_theory, x, jltype_by_sort)

    name = nameof(termcon.declaration)
    return_type = jltype_by_sort[AlgSort(termcon.type)]
    argnames = nameof.(argsof(termcon))
    argnames′ = Array{Symbol}(undef, length(getcontext(termcon)))
    setindex!.(Ref(argnames′), argnames, getvalue.(termcon.args))
    args = [:($k::$v) for (k, v) in zip(argnames, sig.types)]
    impl = to_call_impl(fx.val, codom_theory, codom_module, argnames′, true)

    JuliaFunction(;name, args, return_type, impl)
  end
  instance_code = generate_instance(
    dom_theory,
    dom_module,
    jltype_by_sort,
    new_model_name,
    [],
    Expr(:block, generate_function.([typecon_funs...,
                                     termcon_funs..., 
                                     accessor_funs...
                                     ])...);
    typecheck=true, escape=false
  )

  eval(quote 
    struct $new_model_name 
      model::Any
    end
    $instance_code
    $new_model_name($m)
  end)
end

"""
Compile an AlgTerm into a Julia call Expr where termcons (e.g. `f`) are
interpreted as `mod.f[model.model](...)`.
"""
function to_call_impl(t::AlgTerm, theory::GAT, mod::Union{Symbol,Module}, argnames::Vector{Symbol}, migrate::Bool)
  b = bodyof(t)
  if GATs.isvariable(t)
    argnames[getvalue(getlid(b))]
  elseif  GATs.isdot(t)
    impl = to_call_impl(b.body, theory, mod, argnames, migrate)
    if isnamed(b.head)
      Expr(:., impl, QuoteNode(nameof(b.head)))
    else 
      Expr(:ref, impl, getlid(b.head).val)
    end
  else
    args = to_call_impl.(argsof(b), Ref(theory), Ref(mod), Ref(argnames), migrate)
    name = nameof(headof(b))
    newhead = if name ∈ nameof.(structs(theory))
      Expr(:., :($mod), QuoteNode(name))
    else 
      Expr(:ref, :($mod.$name), migrate ? :(model.model) : :model)
    end
    Expr(:call, newhead, args...)
  end
end

function to_call_accessor(t::AlgTerm, x::Symbol, mod::Module)
  b = bodyof(t)
  arg = only(b.args)
  rest = GATs.isvariable(arg) ? x : to_call_accessor(arg, x, mod)
  Expr(:call, Expr(:ref, :($mod.$(nameof(headof(b)))), :(model.model)), rest)
end

end # module
