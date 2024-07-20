module TheoryInterface
export @theory, @signature, Model, invoke_term, AbstractComputeGraph, Id, TypedVar, AlgTermId

using ..Scopes, ..GATs, ..ExprInterop, GATlab.Util
# using GATlab.Util

using MLStyle, StructEquality, Markdown

abstract type Model{Tup <: Tuple} end

abstract type AbstractComputeGraph{Tup <: Tuple} <: Model{Tup} end

function add_term! end

struct Id
  index::UInt32
end

struct TypedVar{T}
  id::Id
  parent::AbstractComputeGraph
end

struct AlgTermId
  content::GATs.Prims.AlgTerm{Id}
end

function TermAppId(rm::ResolvedMethod, args::Vector{Id})
  AlgTermId(GATs.Prims.TermApp{Id}(rm, args))
end

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
          push!(structlines, mk_struct(theory, judgment, fqmn(__module__)))
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

  push!(modulelines, Expr(:toplevel, :(module Meta
    struct T end
    $(constructor_module(theory))

    @doc ($(Markdown.MD)((@doc $(__module__).$doctarget), $docstr))
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
      compute_graph_model_impl(name, newsegment),
      :(@doc ($(Markdown.MD)((@doc $doctarget), $docstr)) $name)
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
    idx = findfirst(==(AlgSort(termcon.type)), PrimSort.(sorts(theory)))
    method(types[idx])
  elseif isnothing(model)
    method(args...)
  else
    method(WithModel(model), args...)
  end
end

"""
Produce a module with an AlgClosure for each declaration in the theory.
"""
function constructor_module(theory::GAT)
  closures = Dict{Ident, AlgClosure}()

  for segment in allscopes(theory)
    for (x, binding) in zip(getidents(segment), getbindings(segment))
      judgment = getvalue(binding)
      if judgment isa AlgDeclaration
        closures[x] = AlgClosure(theory)
      elseif judgment isa AlgTermConstructor
        add_method!(
          closures[judgment.declaration],
          AlgMethod(
            judgment.localcontext,
            TermApp(
              ResolvedMethod(judgment.declaration, x),
              Var.(idents(judgment.localcontext; lid=judgment.args))
            ),
            "",
            judgment.args,
            judgment.type,
          )
        )
      end
    end
  end

  Expr(
    :module,
    true,
    :Constructors,
    Expr(:block, [:(const $(nameof(x)) = $f) for (x, f) in closures]...)
  )
end

function mk_struct(ctx, s::AlgStruct, mod)
  fields = map(argsof(s)) do b
    Expr(:(::), nameof(b), toexpr(ctx, AlgSort(getvalue(b))))
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

function compute_graph_model_impl(module_name::Symbol, segment::GATSegment)
  fndefs = []
  for (x, binding) in zip(getidents(segment), getbindings(segment))
    j = getvalue(binding)
    if j isa AlgTermConstructor
      decl = j.declaration
      sorts = sortsignature(j)

      args = try
        map(sorts) do sort
          sortname = @match sort begin
            PrimSort(m) => nameof(m)
            _ => error("can't yet handle non-primitive sorts")
          end
          (gensym(), sortname)
        end
      catch _
        continue
      end

      argexprs = map(args) do (name, sortname)
        :($name::$(TypedVar){$module_name.$sortname})
      end

      ret_sort = try
        @match AlgSort(j.type) begin
          PrimSort(m) => nameof(m)
          _ => error("can't yet handle non-primitive sorts")
        end
      catch _
        continue
      end

      rm = ResolvedMethod(decl, x)
      push!(fndefs, quote
        function $module_name.$(nameof(decl))(
          m::$(WithModel){<:$(AbstractComputeGraph)},
          $(argexprs...)
        )
          ret_id = $(TheoryInterface).add_term!(
            m.model,
            $(TermAppId)($rm, Id[$((:($x.id) for (x, _) in args)...)])
          )
          TypedVar{$module_name.$ret_sort}(
            ret_id,
            m.model
          )
        end
      end)
    end
  end
  Expr(:block, fndefs...)
end

end
