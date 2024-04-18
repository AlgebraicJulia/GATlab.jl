module TheoryInterface
export @theory, @signature, Model, invoke_term, _rd

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

"""    
`nametag(T::GAT) : Dict{Symbol, ScopeTag}`

Given a GAT `T`, returns a dictionary of names associated with their ScopeTags.

For example, `ThMagma` would yield

    :default => ScopeTag(*)
    :⋅       => ScopeTag(*)

This allows us to safely check if a theory has a name (with `hastag`) and also retrieve the associated tag.

"""
function nametag(T::GAT)
  if !isempty(T)
    names, tags = T.segments.namelookup, T.segments.taglookup
    Tags = merge(map(collect(keys(tags))) do key
      Dict(tags[key] => key)
    end...)
    Dict(k => get(Tags, names[k], nothing) for k in keys(names))
  else
    Dict(:_EMPTY => newscopetag())
  end
end

"""    
`makeidentdict(host::GAT, guest::GAT, renames::Dict{Symbol} : Dict{Ident}`

Accepts a new theory (the "guest"), the main theory we are building (the "host"), and a rename dictionary. Converts the rename dictionary to a reident dictionary. 

This is used by the reident function, which will recurse through the GAT structure to replace idents.

For example, suppose we are building a theory `ThRing` and require `ThCMonoid` for addition and `ThMonoid` for multiplication, along with their respective rename dictionaries. For each guest, we need the nametags for both host and guest so that we can check, for each entry in the dictionary, if the name we wish to change in the guest already exists in the host theory. This allows us to create ScopeTags only when necessary. 

"""
function makeidentdict(host::GAT, guest::GAT, renames::Dict{Symbol}) 
  guest, host = nametag.([guest, host])
  merge(map(collect(keys(renames))) do old
    new = renames[old] 
    tag = haskey(host, new) ? host[new] : newscopetag()
    # TODO get lid
    Dict(Ident(guest[old], LID(1), old) => Ident(tag, LID(1), new))
  end...) 
end


function usetheory!(host::GAT, guest::GAT, renames::Dict{Symbol}=Dict{Symbol,Symbol}())
  if !isempty(renames)
    guest = reident(makeidentdict(host, guest, renames), guest)
  end
  
  for segment in guest.segments.scopes
    if !hastag(host, gettag(segment))
      GATs.unsafe_pushsegment!(host, segment)
    end
  end
end

# """ 
# `rename

# This modifies our dictionary so the values contain both 
# the target symbol as well as the tag
# """
# function renamedict(ident_dict, renames::Dict{Symbol})
#   merge(map(collect(keys(renames))) do key
#     ident = filter(i -> i.name == key, idents) 
#     Dict(key => (renames[key], ident[1].tag))
#   end...)
# end

function expand_theory(parentname, body, __module__)
  theory = if !isnothing(parentname)
    copy(macroexpand(__module__, :($parentname.Meta.@theory)))
  else
    GAT(:_EMPTY)
  end
  for line in body.args
    @match line begin
      # repeated code
      Expr(:using, Expr(:(:), Expr(:(.), other), renames...)) => begin
        othertheory = macroexpand(__module__, :($other.Meta.@theory))
        rename_dict = merge(map(renames) do expr
          @match expr begin
            Expr(:as, Expr(_, fst), snd) => Dict(fst => snd)
            _ => nothing
          end
        end...)
        usetheory!(theory, othertheory, rename_dict) 
      end
      Expr(:using, Expr(:(.), other)) => begin
        othertheory = macroexpand(__module__, :($other.Meta.@theory))
        usetheory!(theory, othertheory)
      end
      _ => nothing
    end
  end
  theory
end

function theory_impl(head, body, __module__)
  (name, parentname) = @match head begin
    (name::Symbol) => (name, nothing)
    Expr(:(<:), name, parent) => (name, parent)
    _ => error("could not parse head of @theory: $head")
  end

  parent = expand_theory(parentname, body, __module__)

  theory = fromexpr(parent, body, GAT; name, current_module=fqmn(__module__))
  newsegment = theory.segments.scopes[end]

  lines = Any[]
  newnames = Symbol[]

  for binding in newsegment
    judgment = getvalue(binding)
    bname = nameof(binding)
    if judgment isa Union{AlgDeclaration, Alias}
      push!(lines, juliadeclaration(bname))
      push!(newnames, bname)
    end
  end

  modulelines = Any[]

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

  push!(modulelines, Expr(:toplevel, :(module Meta
    struct T end
    const theory = $theory
    macro theory() $theory end
    macro theory_module() parentmodule(@__MODULE__) end
  end)))


  push!(modulelines, :($(GlobalRef(TheoryInterface, :GAT_MODULE_LOOKUP))[$(gettag(newsegment))] = $name))

  esc(
    Expr(
      :toplevel,
      lines...,
      :(
        module $name
        $(modulelines...)
        end
      ),
      :(Core.@__doc__ $(name)),
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

end
