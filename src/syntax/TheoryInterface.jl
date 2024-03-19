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

function theory_impl(head, body, __module__)
  (name, parentname) = @match head begin
    (name::Symbol) => (name, nothing)
    Expr(:(<:), name, parent) => (name, parent)
    _ => error("could not parse head of @theory: $head")
  end
:L
  ## ThAb <: ThMonoid  
  parent = if !isnothing(parentname)
    macroexpand(__module__, :($parentname.Meta.@theory))
  else
    GAT(:_EMPTY)
  end
  ## need to filter out methods already loaded, e.g., ThAbs <: ThSert

# Expr(:using, m) => begin
        #   # I get a weird expression if I just use m 
        #   mod = m.args[1]
        #   th = macroexpand(__module__, :($mod.Meta.@theory))
        #   ## TODO this pattern is used in repr as well.
        #   for seg in th.segments.scopes
        #       block = toexpr(th, seg)
        #       for line in block.args
        #         push!(inherited, line)
        #       end
        #   end
        # end


  # @theory ThRig <: ThSet begin
  #   using ThCMonoid: ⋅ as +, e as zero
  #   using ThMonoid: ⋅ as *, e as one
  #   a * (b + c) == (a * b) + (a * c) ⊣ [a,b,c]
  # end
 
  ## this whole deal should be in a function acting on "body"
  ## initialize vector for storing inherited axioms
  inherited = Any[]
  ## filter out using statements. avoid pesky LNNs
  nonempty_body = filter(u -> typeof(u) != LineNumberNode, body.args)
  any_using = filter(u -> u.head == :using, nonempty_body)
  if !isnothing(any_using)
    # for every using line
    for t ∈ any_using
      @match t begin
        Expr(:using, m) => begin
          # extract module name
          mod = m.args[1].args[1]
          popfirst!(m.args)
          # initialize array of pairs for replacement
          array = Any[]
          for expr ∈ m.args
              # TODO this would probably be better as a do block
              key = string(expr.args[1].args[1])
              val = string(expr.args[2])
              # if "e" or "i" we want to make sure we don't
              # get "default" -> "donefault"
              row = if isletter(key[1])
                  key*"()" => val*"()"
              else
                  key => val
              end
              ## TODO this does work for "default as Ob"
              # row = string(expr.args[1].args[1]) => expr.args[2]
              push!(array, row)
          end
          # pull the args from the theory block
          th = macroexpand(__module__, :($mod.Meta.@theory))
          for seg in th.segments.scopes
            block = toexpr(th, seg)
            for line in block.args
              # TODO i'd like a more principled way of replacing terms than
              # acting on constructed term. For example, instead of
              #   replace("e()::default ⊣ []", "e()" => "zero()")
              # i'd like: pretend term = "e()::default ⊣ []" then I'd like to overload
              # replace for GAT terms 
              #   replace(term, e, zero)
              #   
              newline = Meta.parse(replace(string(line), array...))
              push!(inherited, newline)
            end
            # i'd like to separate the algebraic terms 
            # push!(inherited, length(inherited)+1)
          end
        end
        _ => nothing
      end
    end
  end
  ## 
  unique_inherited = unique(inherited)
  ## i'd rather insert the args into the :using stmt
  for expr in reverse(unique_inherited)
    pushfirst!(body.args, expr)
  end

  theory = fromexpr(parent, body, GAT; name, current_module=fqmn(__module__))
  newsegment = theory.segments.scopes[end]
  docstr = repr(theory)

  lines = Any[]
  newnames = Symbol[]
  structlines = Expr[]
  structnames = Set([nameof(s.declaration) for s in structs(theory)])
  for binding in newsegment
    judgment = getvalue(binding)
    bname = nameof(binding)
    if judgment isa Union{AlgDeclaration, Alias} && bname ∉ structnames
      push!(lines, juliadeclaration(bname))
      push!(newnames, bname)
    elseif judgment isa AlgStruct 
      push!(structlines, mk_struct(judgment, fqmn(__module__)))
    end
  end

  modulelines = Any[]

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

  if !isnothing(parentname)
    push!(modulelines, Expr(:using, Expr(:(.), :(.), :(.), parentname)))
  end
  
  doctarget = gensym()

  push!(modulelines, Expr(:toplevel, :(module Meta
    struct T end
   
    @doc ($(Markdown.MD)((@doc $(__module__).$doctarget), $docstr))
    const theory = $theory

    macro theory() $theory end
    macro theory_module() parentmodule(@__MODULE__) end
  end)))

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
