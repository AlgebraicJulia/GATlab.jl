
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

A struct called `Meta.Wrapper` which is a smart constructor for Julia types 
which implement the theory.
"""
module TheoryInterface
export @theory, @signature, @model_method, invoke_term, wrapper, ModelWrapper, WithModel

using ..Scopes, ..GATs, ..ExprInterop, GATlab.Util

using MLStyle, StructEquality, Markdown
import AlgebraicInterfaces: getvalue

@struct_hash_equal struct WithModel{M}
  model::M
end

getvalue(m::WithModel) = m.model

function implements end # implemented in ModelInterface

function impl_type end # implemented in ModelInterface

function impl_types end # implemented in ModelInterface

""" Parse markdown coming out of @doc programatically. """
mdp(::Nothing) = ""
mdp(x::Markdown.MD) = x
function mdp(x::Base.Docs.DocStr)
  Markdown.parse(only(x.text))
end


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
    Expr(:import,
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
  wrapper_expr = wrapper(name, theory, fqmn(__module__))
  push!(modulelines, Expr(:toplevel, :(module Meta
    struct T end
   
    const theory = $theory

    macro theory() $theory end
    macro theory_module() parentmodule(@__MODULE__) end

    $wrapper_expr
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
          $(structlines...)
          $(modulelines...)
        end
      ),
      :(@doc ($(Markdown.MD)($mdp(@doc $doctarget), $docstr)) $name)
    )
  )
end

"""
The Dispatch model defers to type-dispatch: f[Dispatch](a,b,c) == f(a,b,c)
"""
@struct_hash_equal struct Dispatch
  jltypes::Dict{AlgSort, Type}
end

Dispatch(theory_module::Module, types::AbstractVector{<:Type}) = 
  Dispatch(theory_module.Meta.theory, types)

function Dispatch(theory_module::GAT, types::AbstractVector{<:Type}) 
  s = sorts(theory_module)
  length(s) == length(types) || error("Bad length of type vector")
  Dispatch(Dict(zip(s, types)))
end

"""
The Initial model assigns `Union{}` to all AlgSorts. There is one implementation
for any given theory.
"""
@struct_hash_equal struct InitialModel′ end

"""
The Terminal model assigns `Nothing` to all AlgSorts. There is one 
implementation for any given theory.
"""
@struct_hash_equal struct TerminalModel′ end
 

# Register methods for getindex even if not part of any theory
macro model_method(name) esc(juliadeclaration(name))
end

# WARNING: if any other package play with indexing methodnames with their own 
# structs, then this code could be broken because it assumes we are the only  
# ones to use this trick.
function juliadeclaration(name::Symbol)
  funname = gensym(name)
  quote
    function $name end
    # we expect just one method because of Dispatch type
    if isempty(Base.methods(Base.getindex, [typeof($name), Any]))
      Base.getindex(f::typeof($name), ::$(GlobalRef(TheoryInterface, :Dispatch))) = f
      Base.getindex(f::typeof($name), ::$(GlobalRef(TheoryInterface, :InitialModel′))) = (x...;kw...)->error("Cannot call")
      Base.getindex(f::typeof($name), ::$(GlobalRef(TheoryInterface, :TerminalModel′))) = (x...;kw...)->nothing

      function Base.getindex(::typeof($name), m::Any)
        function $funname(args...; context=nothing) 
          $name($(GlobalRef(TheoryInterface, :WithModel))(m), args...; context)
        end
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

# Wrapper type 
##############


function wrapper(name::Symbol, t::GAT, mod)
  use = Expr(:using, Expr(:., :., :., name))
  quote
    $use
    macro wrapper(n)
      x, y = $(parse_wrapper_input)(n)
      esc(:($($(name)).Meta.@wrapper $x $y))
    end

    macro typed_wrapper(n)
      x, y = $(parse_wrapper_input)(n)
      esc(:($($(name)).Meta.@typed_wrapper $x $y))
    end

    macro wrapper(n, abs)
      doctarget = gensym()
      Ts = ($(sorts)($t))
      Xs = map(Ts) do s 
        :($(GlobalRef($(TheoryInterface), :impl_type))(x, $s))
      end

      esc(quote 
        # Catch any potential docs above the macro call
        const $(doctarget) = nothing
        Core.@__doc__ $(doctarget)

        # Declare the wrapper struct
        struct $n <: $abs
          val::Any
          function $n(x::Any)
            try $($(GlobalRef(TheoryInterface, :implements)))(x, $($name), [$(Xs...)]) 
            catch MethodError false end || error("Invalid $($($(name))) model: $x")
            new(x)
          end
        end
        # Apply the caught documentation to the new struct
        @doc $($(mdp))(@doc $doctarget) $n

        # Define == and hash
        $(Expr(:macrocall, $(GlobalRef(StructEquality, Symbol("@struct_hash_equal"))), $(mod), $(:n)))

        # GlobalRef doesn't work: "invalid function name".
        GATlab.getvalue(x::$n) = x.val 
        GATlab.impl_type(x::$n, o::Symbol) = GATlab.impl_type(x.val, $($name), o)

        # Dispatch on model value for all declarations in theory
        $(map(filter(x->x[2] isa $AlgDeclaration, $(identvalues(t)))) do (x,j)
          if j isa $(AlgDeclaration) 
            op = nameof(x)
            :($($(name)).$op(x::$(($(:n))), args...; kw...) = 
              $($(name)).$op[x.val](args...; kw...))
          end
      end...)
      nothing
      end)
    end

    macro typed_wrapper(n, abs)
      doctarget = gensym()
      Ts = nameof.($(sorts)($t))
      Xs = map(Ts) do s 
        :($(GlobalRef($(TheoryInterface), :impl_type))(x, $($(name)), $($(Meta.quot)(s))))
      end
      XTs = map(zip(Ts,Xs)) do (T,X)
        :($X <: $T || error("Mismatch $($($(Meta.quot)(T))): $($X) ⊄ $($T)"))
      end
      esc(quote 
        # Catch any potential docs above the macro call
        const $(doctarget) = nothing
        Core.@__doc__ $(doctarget)

        # Declare the wrapper struct
        struct $n{$(Ts...)} <: $abs
          val::Any
          function $n{$(Ts...)}(x::Any) where {$(Ts...)}
            $($(GlobalRef(TheoryInterface, :implements)))(x, $($name), [$(Xs...)]) || error("Invalid $($($(name))) model: $x")
            $(XTs...)
            # TODO? CHECK THAT THE GIVEN PARAMETERS MATCH Xs?
            new{$(Ts...)}(x)
          end

          function $n(x::Any) 
            $($(GlobalRef(TheoryInterface, :implements)))(x, $($name), [$(Xs...)]) || error("Invalid $($($(name))) model: $x")
            new{$(Xs...)}(x)
          end
        end
        # Apply the caught documentation to the new struct
        @doc $($(mdp))(@doc $doctarget) $n

        # Define == and hash
        $(Expr(:macrocall, $(GlobalRef(StructEquality, Symbol("@struct_hash_equal"))), $(mod), $(:n)))

        # GlobalRef doesn't work: "invalid function name".
        GATlab.getvalue(x::$n) = x.val 
        GATlab.impl_type(x::$n, o::Symbol) = GATlab.impl_type(x.val, $($name), o)

        # Dispatch on model value for all declarations in theory
        $(map(filter(x->x[2] isa $AlgDeclaration, $(identvalues(t)))) do (x,j)
          if j isa $(AlgDeclaration) 
            op = nameof(x)
            :($($(name)).$op(x::$(($(:n))), args...; kw...) = 
              $($(name)).$op[x.val](args...; kw...))
          end
      end...)
      nothing
      end)
    end
  end
end

parse_wrapper_input(n::Symbol) = n, Any
parse_wrapper_input(n::Expr) = n.head == :<: ? n.args : error("Bad input for wrapper")


end # module
