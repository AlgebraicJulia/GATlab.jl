module TheoryInterface
export @theory, @signature, @rename, Model, invoke_term, _rd, nametag, makerenamedict

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
Renaming a theory can be done with the @theory macro:

  ```
  @theory ThNewName begin
    using: ThTheory: using old as new, before as after
  end
  ```

@rename simplifies this expression by one line:

  ```
  @rename ThNewName using ThTheory: using old as new, before as after
  ```

"""
macro rename(newname, body)
  rename_impl(newname, body, __module__)
end

# @rename ThM using ThMonoid using ⋅ as *
function rename_impl(newname, body, __module__) 
 
  # validate head and body
  newname isa Symbol || error("$newname must be a symbol")
  !isdefined(__module__, newname) || error("$newname cannot be defined already")

  parent = expand_theory(nothing, body, __module__)
  newtheory = fromexpr(parent, body, GAT; name=newname, current_module=fqmn(__module__))

  #
  lines = Any[]
  newnames = Symbol[]

  ## XXX "for binding in segment" was "... in newsegment", and I wrapped this
  ## in a for-loop for segments. This was done to debug an issue with ModelInterface
  ## where the `default` function was not being declared.
  ##
  ## owen: this should be in newsegment as before
  for segment in newtheory.segments.scopes
    for binding in segment
      judgment = getvalue(binding)
      bname = nameof(binding)
      if judgment isa Union{AlgDeclaration, Alias}
        push!(lines, juliadeclaration(bname))
        push!(newnames, bname)
      end
    end
  end

  modulelines = Any[]

  push!(modulelines, :(export $(allnames(newtheory; aliases=true)...)))

  push!(
   modulelines,
   Expr(:using,
     Expr(:(:),
       Expr(:(.), :(.), :(.), nameof(__module__)),
       Expr.(Ref(:(.)), newnames)...
     )
   )
  )

  push!(modulelines, Expr(:toplevel, :(module Meta
    struct T end
    const theory = $newtheory
    macro theory() $newtheory end
    macro theory_module() parentmodule(@__MODULE__) end
  end)))

  esc(
    Expr(
      :toplevel,
      lines...,
      :(
        module $newname
        $(modulelines...)
        end
      ),
      :(Core.@__doc__ $(newname)),
     )
   )
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
  if !isempty(T.segments.scopes)

    merge(filter(!isnothing, map(T.segments.scopes) do scope
      k = collect(keys(scope.scope.names));
      if !isempty(k)
        Dict(k[1] => scope.scope.tag)
      end
    end)...)
    # names, tags = T.segments.namelookup, T.segments.taglookup
    # Tags = merge(map(collect(keys(tags))) do key
    #   Dict(tags[key] => key)
    # end...)
    # Dict(k => get(Tags, names[k], nothing) for k in keys(names))
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
function makeidentdict(host::GAT, guest::GAT, renames::Dict{Symbol,Symbol}; is_reident::Bool=true)
  host_nametag, guest_nametag = nametag(host), nametag(guest)
  merge(map(collect(keys(renames))) do old
    new = renames[old]
    if is_reident
      tag = haskey(host_nametag, new) ? host_nametag[new] : (haskey(guest_nametag, new) ? guest_nametag[new] : newscopetag()) # TODO we don't want to want to make new scopetag
      Dict(Ident(guest_nametag[old], LID(1), old) => Ident(tag, LID(1), new)) # TODO get lid
    else
      Dict(Ident(guest_nametag[old], LID(1), old) => Ident(guest_nametag[old], LID(1), new))
    end
  end...) 
end
# TODO if there is a collision, choose same scope tag

function usetheory!(host::GAT, guest::GAT, renames::Dict{Symbol,Symbol}=Dict{Symbol,Symbol}())
  if !isempty(renames)
    guest = reident(makeidentdict(host, guest, renames), guest)
  end
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

  # collect renames
  for line in body.args
    @match line begin
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
    Expr(:(<:), name, parent) => (name, parent) # TODO make parents
    _ => error("could not parse head of @theory: $head")
  end

  parent = expand_theory(parentname, body, __module__)

  theory = fromexpr(parent, body, GAT; name, current_module=fqmn(__module__))


  newsegment = theory.segments.scopes[end]
  # @info "NEWSEGMENT" newsegment
  docstr = repr(theory)

  lines = Any[]
  newnames = Symbol[]
  structlines = Expr[]
  structnames = Set([nameof(s.declaration) for s in structs(theory)])
  for scope in theory.segments.scopes
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

  # TODO deprecated?
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
