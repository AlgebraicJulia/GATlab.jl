
"""
Any Julia struct can be a model of a GAT. A model `m::M` is marked as 
implementing a theory iff, for all operations f(::A,::B,...), we have:

`hasmethod(f, (WithModel{M}, A, B) == true`

Then we expect the following.

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

export implements, impl_type, impl_types,
       @model, @instance, @withmodel, migrate_model, @default_model

using ...Syntax
using ...Util.MetaUtils
using ...Util.MetaUtils: JuliaFunctionSigNoWhere

using ...Syntax.TheoryMaps: dom, codom
using ...Syntax.TheoryInterface: GAT_MODULE_LOOKUP, WithModel
import ...Syntax.TheoryInterface: implements, impl_type, impl_types

using MLStyle
using DataStructures: DefaultDict, OrderedDict

"""
Check whether a model implements a particular theory.

If no types are provided, then we look up whether or not `impl_type` methods 
exist for this model + theory. If not, we will get a MethodError and assume 
that the model does not implement the theory. (WARNING: occasionally one has 
a complex type, such as `foo(Int,String)` which itself leads to a MethodError, 
and this can be confusing because it looks like the model doesn't implement
the theory at all rather than just being an error in how it was implemented).

Once types are provided, we can check whether the theory is implemented by 
checking for each term constructor whether or not the model implements that
(handled by a different `implements` method).
"""
function implements(m, theory_module::Module, types = nothing)
  T = theory_module.Meta.theory 
  try 
    types = isnothing(types) ? impl_types(m, T) : types
  catch e
    e isa MethodError && return false
    throw(e)
  end
    return all(t -> implements(m, theory_module, t, types), last.(termcons(T)))
end 

""" User-friendly access to checking if a model implements an operation.

Throws an error if the name is overloaded. Anything programmatic should be 
calling a method which accepts method `Ident`s rather than `Symbol`s.
"""
function implements(m::T, theory_mod::Module, name::Symbol, types=nothing) where T
  isnothing(types) || return _implements(m, theory_mod, name, types)
  theory = theory_mod.Meta.theory
  decl = ident(theory; name)
  args, _ = only(theory.resolvers[decl])
  return !isempty(methods(getfield(theory_mod, name),
                          (WithModel{T}, fill(Any, length(args))...)))
end

function _implements(::T, theory::Module, name::Symbol, types::Vector{<:Type}) where T
  f = getfield(theory, name)
  any(==(Union{}), types) && return true # no such methods (Julia 1.10 bug)
  hasmethod(f, Tuple{WithModel{<:T}, types...}, (:context,))
end

""" 
Machine-friendly access to checking if a model implements a particular
operation. The `types` vector is in bijection with the AlgSorts of the
*whole theory*. 
"""  
function implements(m, theory::Module, x::Ident, types::Vector{<:Type})
  tc = getvalue(theory.Meta.theory[x])
  name = nameof(getdecl(tc))
  typedict = Dict(zip(sorts(theory.Meta.theory), types))
  types′ = Type[typedict[AlgSort(getvalue(tc[i]))] for i in tc.args]
  return _implements(m, theory, name, types′)
end


"""
If `m` implements a GAT with a type constructor (identified by ident `id`), 
mapped to a Julia type, this function returns that Julia type.
"""
impl_type(m, x::Ident) = impl_type(m, Val{gettag(x)}, Val{getlid(x)})

impl_type(m, x::AlgSort) = impl_type(m, methodof(x))

impl_types(m, T::Module) = impl_types(m, T.Meta.theory)

impl_types(m, T::GAT) = map(sorts(T)) do s 
  t = impl_type(m, s) 
  t isa Type || error("$s impl_type not a Type: $t")
  t
end

""" This can error if called on a symbol that matches a declaration that has more than one method """
function impl_type(m, mod::Module, name::Symbol) 
  T = mod.Meta.theory
  impl_type(m, last(only(T.resolvers[ident(mod.Meta.theory; name)])))
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
  ...
end
```

"""
macro instance(head, model, body)
  # Parse the head of @instance to get theory and instance types
  (theory_module, instance_types) = @match head begin
    Expr(:curly, ThX, Expr(:(=), a,b),xs...) => begin
      theory = macroexpand(__module__, :($ThX.Meta.@theory))
      nS, nT = length(primitive_sorts(theory)), length(xs)+1 
      nS == nT || error("$nT types provided ($ThX expected $nS)")
      ThX => map(nameof.(primitive_sorts(theory))) do psort
        for x in [Expr(:(=), a,b); xs]
          x.head == :(=) || error("Unexpected type assignment $x")
          n, v = x.args
          n == psort && return v
        end
        error("Sort $psort not found in $xs")
      end
    end
    :($ThX{$(Ts...)}) =>  (ThX, Ts) 
    _ => error("invalid syntax for head of @instance macro: $head")
  end

  # Get the underlying theory
  theory = macroexpand(__module__, :($theory_module.Meta.@theory))

  nS, nT = length(primitive_sorts(theory)), length(instance_types) 
  nS == nT || error("$nT types provided ($theory_module expected $nS)")

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
  escape=true
)
  # The old (Catlab) style of instance, where there is no explicit model
  oldinstance = isnothing(model_type)

  # Parse the body into functions defined here and functions defined elsewhere
  typechecked_functions = parse_instance_body(body, theory)
  methodnames = Vector{Symbol}(nameof.(typechecked_functions))
  # Adds keyword arguments to the functions, and qualifies them by
  # `theory_module`, i.e. changes
  # `Ob(x) = blah`
  # to
  # `ThCategory.Ob(m::WithModel{M}, x; context=nothing) = let model = m.model in blah end`
  qualified_typecons = []
  qualified_functions = []
  for f in typechecked_functions
    x = ident(theory; name =nameof(f)) 
    # This could go awry if the same name is used as both a typecon and termcon
    tc = getvalue(theory[last(first(theory.resolvers[x]))]) 
    qf = qualify_function(f, theory_module, model_type, whereparams, 
                          Set(nameof.(structs(theory))))
    if tc isa AlgTermConstructor 
      push!(qualified_functions, qf)
    else 
      push!(qualified_typecons, qf)
    end
  end

  type_aliases, term_aliases = make_alias_definitions(
      theory, theory_module, jltype_by_sort, model_type, whereparams, methodnames)

  impl_type_declarations = if isnothing(model_type) 
    Expr[]
  else 
    map(collect(jltype_by_sort)) do (k, v)
      impl_type_declaration(model_type, whereparams, k, v)
    end
  end

  runtime_impl_checks = map(last.(termcons(theory))) do x
      typecheck_runtime(theory_module, theory, model_type, whereparams, x, jltype_by_sort)
  end

  docsink = gensym(:docsink)

  code = Expr(:block,
    generate_function.(qualified_typecons)...,
    generate_function.(qualified_functions)...,
    generate_function.(type_aliases)...,
    generate_function.(term_aliases)...,
    runtime_impl_checks...,
    impl_type_declarations...,
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
  for elem in strip_lines(expr).args
    elem = strip_lines(elem)
    fun = parse_function(elem)
    fun = setname(fun, nameof(ident(theory; name=fun.name)))
    push!(funs, fun)
  end
  return funs
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

"""
Returns two lists of JuliaFunctions: one for aliases of type constructors, one 
for aliases of term constructors.

Optional `methodnames` argument restricts aliases to only being generated if the 
name they are an alias for is included in this list.
"""
function make_alias_definitions(theory, theory_module, jltype_by_sort, model_type, 
                                whereparams, methodnames=nothing)
  typelines, termlines = [], []
  oldinstance = isnothing(model_type)
  for segment in theory.segments.scopes
    for binding in segment
      alias = getvalue(binding)
      name = nameof(binding)
      if alias isa Alias && (isnothing(methodnames) || nameof(alias.ref) ∈ methodnames)
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
          is_term = getvalue(theory[method]) isa AlgTermConstructor
          push!(is_term ? termlines : typelines, overload)
        end
      end
    end
  end
  typelines, termlines
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
      ($(model_type) where {$(whereparams...)}, Type{Val{$(gettag(methodof(sort)))}}, Type{Val{$(getlid(methodof(sort)))}}))
      $(GlobalRef(ModelInterface, :impl_type))(
          ::$(model_type), ::Type{Val{$(gettag(methodof(sort)))}}, ::Type{Val{$(getlid(methodof(sort)))}}
        ) where {$(whereparams...)} = $(jltype)
    end
  end
end

""" Check if a method exists """
function typecheck_runtime(theory_name, theory::GAT, model_type, whereparams, x::Ident, jltype)
  isempty(structs(theory)) || return :() # can't handle EqTypes yet
  tc = getvalue(theory[x])
  name = nameof(getdecl(tc))
  wm = :($(GlobalRef(ModelInterface, :WithModel)){$model_type})
  jltypes = [jltype[AlgSort(getvalue(i))] for i in argsof(tc)]

  # For default models, nullary constructors are handled funnily
  isnothing(model_type) && isempty(jltypes) && return :()

  jltypes′ = isnothing(model_type) ? jltypes : [wm, jltypes...]
  jltypes′′ = map(jltypes) do t 
    Expr(:where, t, whereparams...)
  end
  quote
    any(==(Union{}), [$(jltypes′′...)]) || hasmethod($(theory_name).$(name), Tuple{$(jltypes′...)} where {$(whereparams...)}, (:context,)) || error(
      "No implementation for $($(theory_name)) $($(theory_name).$(name)) with arg types:\n"*join(string.([$(jltypes′′...)]), "\n")
    )
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
    v => :(impl_type($m, AlgSort($F($v.method).val)))
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
    escape=false
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


# Default models

"""
Create an @instance for a model `M` whose methods are determined by type 
dispatch, e.g.:

```
@instance ThCategory{O,H} [model::M] begin
  id(x::O) = id(x)
  compose(f::H, g::H)::H = compose(f, g)
end
```

Use this with caution! For example, using this with two different models of 
the same theory with the same types would cause a conflict.
"""
function default_instance(theorymodule, theory, jltype_by_sort, model)
  acc = Iterators.flatten(values.(values(theory.accessors)))

  termcon_funs = map(last.(termcons(theory)) ∪ acc) do x 
    generate_function(use_dispatch_method_impl(x, theory, jltype_by_sort))
  end
  generate_instance(
    theory, theorymodule, jltype_by_sort, model, [], 
    Expr(:block, termcon_funs...); escape=true)
end

"""
Create an @instance for a model `M` whose methods are determined by the 
implementation of another model, `M2`, e.g.:

```
@instance ThCategory{O,H} [model::M] begin
  id(x::O) = id[M2](x)
  compose(f::H, g::H)::H = compose[M2](f, g)
end
```
"""
function default_model(theorymodule, theory, jltype_by_sort, model)
  acc = Iterators.flatten(values.(values(theory.accessors)))
  termcon_funs = map(last.(termcons(theory)) ∪ acc) do x 
    generate_function(use_model_method_impl(x, theory, jltype_by_sort, model))
  end
  generate_instance(
    theory, theorymodule, jltype_by_sort, nothing, [], 
    Expr(:block, termcon_funs...);  escape=true)
end

macro default_model(head, model)
  # Parse the head of @instance to get theory and instance types
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
  m = parse_model_param(model)[1]

  # Create the actual instance
  default_model(theory_module, theory, jltype_by_sort, m)
end

"""
A canonical implementation that just calls the method with the implementation
of another model, `m`.
"""
function use_model_method_impl(x::Ident, theory::GAT, 
                               jltype_by_sort::Dict{AlgSort}, m::Expr0)
  op = getvalue(theory[x])
  name = nameof(getdecl(op))
  return_type = op isa AlgAccessor ? nothing : jltype_by_sort[AlgSort(op.type)]
  args = args_from_sorts(sortsignature(op), jltype_by_sort)
  impl = :(return $(name)[$m()]($(args...)))
  JuliaFunction(name=name, args=args, return_type=return_type, impl=impl)
end

"""
A canonical implementation that just calls the method with type dispatch.
"""
function use_dispatch_method_impl(x::Ident, theory::GAT, 
                                  jltype_by_sort::Dict{AlgSort})
  op = getvalue(theory[x])
  name = nameof(getdecl(op))
  return_type = op isa AlgAccessor ? nothing : jltype_by_sort[AlgSort(op.type)]
  args = args_from_sorts(sortsignature(op), jltype_by_sort)
  impl = :(return $(name)($(args...)))
  JuliaFunction(name=name, args=args, return_type=return_type, impl=impl)
end


end # module
