module Scopes
export
  ScopeTag, newscopetag, retag, rename,
  ScopeTagError,
  LID,
  Ident, gettag, getlid, isnamed,
  Binding, getvalue, setvalue, getsignature, getline, setline,
  Context, getscope, nscopes, getlevel, hasname, hastag,
  HasContext, getcontext,
  hasident, ident, getidents, idents, canonicalize,
  HasScope, haslid, getscope, getbindings, getbinding,
  sigtype, identvalues, namevalues,
  Scope, ScopeList, HasScopeList, AppendScope,
  EmptyContext

using UUIDs
using MLStyle
using StructEquality
using Crayons
import Base: rest

using ...Util

# ScopeTags
###########

"""
The tag that makes reference to a specific scope possible.
"""
@struct_hash_equal struct ScopeTag
  val::UUID
end

newscopetag() = ScopeTag(uuid4())

const DARK_MODE = Ref(true)

function tagcrayon(tag::ScopeTag)
  lightnessrange = if DARK_MODE[]
    (50., 100.)
  else
    (0., 50.)
  end
  hashcrayon(tag; lightnessrange, chromarange=(50., 100.))
end

function Base.show(io::IO, tag::ScopeTag)
  print(io, "ScopeTag(")
  if get(io, :color, true)
    crayon = tagcrayon(tag)
    print(io, crayon, "•")
    print(io, inv(crayon))
  else
    print(io, tag.val)
  end
  print(io, ")")
end

"""
`retag(replacements::Dict{ScopeTag, ScopeTag}, x::T) where {T} -> T`

Recurse through the structure of `x`, swapping any instance of a ScopeTag `t`
with `get(replacements, t, t)`. Overload this function on structs that have
ScopeTags within them.
"""
retag(replacements::Dict{ScopeTag, ScopeTag}, x) = x

"""
`rename(tag::ScopeTag, replacements::Dict{Symbol, Symbol}, x::T) where {T} -> T`

Recurse through the structure of `x`, and change any name `n` in scope `tag` to
`get(replacements, n, n)`. Overload this function on structs that have names
in them.
"""
rename(tag::ScopeTag, replacements::Dict{Symbol, Symbol}, x) = x

"""
`ScopeTagError`

An error to throw when an identifier has an unexpected scope tag
"""
struct ScopeTagError <: Exception
  expectedcontext::Any
  thing::Any
end

Base.showerror(io::IO, e::ScopeTagError) =
  print(io, "tag from ", e.thing, " does not match anything in ", e.expectedcontext)

# Local IDs
###########

"""
A LID (Local ID) indexes a given scope.

Currently, scopes assign LIDs sequentially -- this is not a stable guarantee
however, and in theory scopes could have "sparse" LIDs.
"""
@struct_hash_equal struct LID
  val::Int
end

function Base.show(io::IO, lid::LID)
  print(io, lid.val)
end

getvalue(lid::LID) = lid.val

# Idents
########

"""
`Ident`

An identifier.

`tag` refers to the scope that this Ident is bound in
`lid` indexes the scope that Ident is bound in
`name` is an optional field for the sake of printing. A variable in a scope
might be associated with several names
"""
struct Ident
  tag::ScopeTag
  lid::LID
  name::Union{Symbol, Nothing}
  function Ident(tag::ScopeTag, lid::LID, name::Union{Symbol, Nothing}=nothing)
    new(tag, lid, name)
  end
end

Base.:(==)(x::Ident, y::Ident) = x.tag == y.tag && x.lid == y.lid

Base.hash(x::Ident, h::UInt64) = hash(x.tag, hash(x.lid, h))

gettag(x::Ident) = x.tag

getlid(x::Ident) = x.lid

Base.nameof(x::Ident) = x.name

isnamed(x::Ident) = !isnothing(nameof(x))

function Base.show(io::IO, x::Ident)
  crayon = if get(io, :color, true)
    tagcrayon(gettag(x))
  else
    Crayon()
  end
  if isnamed(x)
    print(io, crayon, nameof(x))
  else
    print(io, crayon, "#$(getlid(x))")
  end
  print(io, inv(crayon))
end

retag(replacements::Dict{ScopeTag, ScopeTag}, x::Ident) =
  if gettag(x) ∈ keys(replacements)
    Ident(replacements[gettag(x)], getlid(x), nameof(x))
  else
    x
  end

rename(tag::ScopeTag, replacements::Dict{Symbol, Symbol}, x::Ident) =
  if gettag(x) == tag && nameof(x) ∈ keys(replacements)
    Ident(tag, getlid(x), replacements[nameof(x)])
  else
    x
  end

# Bindings
##########

"""
`Binding{T, Sig}`

A binding associates some `T`-typed value to a name,
disambiguated by a signature in `Sig` in the case of overloading.

`primary` is an optional distinguished name
`value` is the element
`sig` is a way of uniquely distinguishing this element from others with the same name 
(for example, ⊗ : Ob x Ob -> Ob and Hom x Hom -> Hom)
"""
@struct_hash_equal struct Binding{T, Sig}
  primary::Union{Symbol, Nothing}
  value::T
  sig::Sig
  line::Union{LineNumberNode, Nothing}
  function Binding{T, Sig}(
    primary::Union{Symbol, Nothing},
    value::T,
    sig::Sig=nothing,
    line::Union{LineNumberNode, Nothing}=nothing
  ) where {T, Sig}
    new{T, Sig}(primary, value, sig, line)
  end
  function Binding{T}(
    primary::Union{Symbol, Nothing},
    value::T,
    sig::Sig=nothing,
    line::Union{LineNumberNode, Nothing}=nothing
  ) where {T, Sig}
    Binding{T,Sig}(primary, value, sig, line)
  end
end

"""Type for printing out bindings with colored keys"""
@struct_hash_equal struct ScopedBinding 
  scope::ScopeTag 
  binding::Binding
end

Base.show(io::IO, b::ScopedBinding) = 
  Base.show(io, b.binding; crayon=tagcrayon(b.scope))

function Base.show(io::IO, b::Binding; crayon=nothing)
  bname = isnothing(nameof(b)) ? "_" : nameof(b)
  if isnothing(crayon) || !(get(io, :color, true))
    print(io, bname)
  else 
    print(io, crayon, bname)
    print(io, inv(crayon))
  end
  print(io, isnothing(getsignature(b)) ? "" : "::$(getsignature(b))")
  print(io, " => $(repr(getvalue(b)))")
end

Base.nameof(b::Binding) = b.primary

MetaUtils.setname(b::Binding{T, Sig}, name::Symbol) where {T, Sig} =
  Binding{T, Sig}(name, b.value, b.sig, b.line)

getvalue(b::Binding) = b.value

getsignature(b::Binding) = b.sig

retag(replacements::Dict{ScopeTag, ScopeTag}, binding::Binding{T, Sig}) where {T, Sig} =
  Binding{T,Sig}(
    nameof(binding),
    retag(replacements, getvalue(binding)),
    retag(replacements, getsignature(binding))
  )

getline(b::Binding) = b.line

setline(b::Binding{T, Sig}, line::Union{LineNumberNode, Nothing}) where {T, Sig} =
  Binding{T, Sig}(b.primary, b.value, b.sig, line)
setvalue(b::Binding{T, Sig}, t::T) where {T,Sig} = 
  Binding{T, Sig}(b.primary, t, b.sig, b.line)

# Context
#########

"""
A `Context` is anything which contains an ordered list of scopes.

Scopes within a context are referred to by *level*, which is their index within
this list.

`Context`s should overload:

- `getscope(c::Context, level::Int) -> Scope`
- `nscopes(c::Context) -> Int`
- `hastag(c::Context, tag::ScopeTag) -> Bool`
- `hasname(c::Context, name::Symbol) -> Bool`
- `getlevel(c::Context, tag::ScopeTag) -> Int`
- `getlevel(c::Context, name::Symbol) -> Int`
"""
abstract type Context{T, Sig} end

abstract type HasContext{T, Sig} <: Context{T, Sig} end

function getcontext end

getscope(hc::HasContext, level::Int) = getscope(getcontext(hc), level)

nscopes(hc::HasContext) = nscopes(getcontext(hc))

hastag(hc::HasContext, tag::ScopeTag) = hastag(getcontext(hc), tag)

hasname(hc::HasContext, name::Symbol) = hasname(getcontext(hc), name)

getlevel(hc::HasContext, tag::ScopeTag) = getlevel(getcontext(hc), tag)

getlevel(hc::HasContext, name::Symbol) = getlevel(getcontext(hc), name)

# HasScope
##########

"""
An abstract type for wrappers around a single scope.

Must overload

`getscope(hs::HasScope) -> Scope`
"""
abstract type HasScope{T, Sig} <: Context{T, Sig} end

getscope(hs::HasScope, x::Int) =
  x == 1 ? getscope(hs) : throw(BoundsError(hs, x))

hastag(hs::HasScope, tag::ScopeTag) = getscope(hs).tag == tag

hasname(hs::HasScope, name::Symbol) = haskey(getscope(hs).primary, name) || haskey(getscope(hs).names, name)

getlevel(hs::HasScope, tag::ScopeTag) =
  if hastag(hs, tag)
    1
  else
    throw(KeyError(tag))
  end

getlevel(hs::HasScope, name::Symbol) =
  if hasname(hs, name)
    1
  else
    throw(KeyError(name))
  end

nscopes(hs::HasScope) = 1

# Scopes
########

"""
`Scope{T, Sig}`

In GATlab, we handle overloading and shadowing with a notion of *scope*.
Names are allowed to overload within a scope, and shadow between scopes.
Anything which binds variables introduces a scope, for instance a `@theory`
declaration or a context. For example, here is a scope with 3 elements:

```
x::Int = 3
y::String = "hello"
x::String = "ex"
```

This is a valid scope even though there are name collisions, because the
signature (in this case, a datatype) disambiguates. Of course, it may not be
wise to disambiguate by type, because it is not always possible to infer
expected type.  In general, one should pick something that can be inferred, and
`Nothing` is always a reasonable choice, which disallows any name collisions.
"""
struct Scope{T, Sig} <: HasScope{T, Sig}
  # unique identifier for the scope
  tag::ScopeTag
  # ordered sequence of name assignments
  bindings::Vector{Binding{T, Sig}}
  # a cached mapping which takes a primary name and a disambiguator (i.e. signature)
  # and returns the index in `bindings`
  names::Dict{Symbol, Dict{Sig, LID}}
  # Maps a primary name to its aliases
  aliases::Dict{Symbol, Set{Symbol}}
  # Maps an alias to its primary name
  primary::Dict{Symbol, Symbol}
  function Scope{T, Sig}(tag, bindings, names, 
                         aliases=Dict{Symbol, Set{Symbol}}(), 
                         primary=nothing) where {T,Sig}
    primary = isnothing(primary) ? make_primary_map(aliases) : primary
    check_names(bindings, names, aliases, primary)
    new{T,Sig}(tag, bindings, names, aliases, primary)
  end
end

check_names(s::Scope) = check_names(s.bindings, s.names, s.aliases, s.primary)
 
function check_names(bindings, names, aliases, primary)
  # Check bindings don't shadow each other
  namevals = Set([(nameof(b), getvalue(b)) for b in bindings])
  shadow = "Scopes do not permit shadowing: $namevals"
  length(namevals) == length(bindings) || error(shadow)

  # Check names are valid 
  allnames = Set(filter(!isnothing, nameof.(bindings)))
  extra_names = setdiff(keys(names), allnames)
  missing_names = setdiff(allnames, keys(names))
  isempty(extra_names) || error("Extra names: $extra_names")
  isempty(missing_names) || error("Missing names: $missing_names")
  
  # Check alias names are valid 
  bad_a_names = setdiff(keys(aliases), allnames)
  isempty(bad_a_names) || error("Bad alias keys: $bad_a_names")
  
  # Check alias values are valid
  aliasvalues = union(Symbol[], values(aliases)...)
  bad_a_values = intersect(aliasvalues, allnames)
  isempty(bad_a_values) || error("Alias / name collision: $bad_a_values")

  # Check that primary names are all valid
  bad_pvals = setdiff(values(primary), keys(names))
  isempty(bad_pvals) || error("Bad primary name values: $bad_pvals")
  
  # Check that primary aliases are all valid 
  bad_pkeys = setdiff(keys(primary), aliasvalues)
  isempty(bad_pkeys) || error("Bad primary name values: $bad_pkeys")
end 

Base.:(==)(s1::Scope, s2::Scope) = s1.tag == s2.tag

Base.hash(s::Scope, h::UInt64) = hash(s.tag, h)

Scope{T, Sig}() where {T, Sig} = 
  Scope{T, Sig}(newscopetag(), Binding{T, Sig}[], Dict{Symbol, Dict{Sig, LID}}())

function make_name_dict(bindings::AbstractVector{Binding{T, Sig}}) where {T, Sig}
  d = Dict{Symbol, Dict{Sig, LID}}()
  for (i, binding) in enumerate(bindings)
    name = nameof(binding)
    if !(name ∈ keys(d))
      d[name] = Dict{Sig, LID}()
    end
    sig = getsignature(binding)
    if sig ∈ keys(d[name])
      error("already defined $name with signature $sig")
    end
    d[name][sig] = LID(i)
  end
  d
end

function make_primary_map(aliases::Dict{Symbol, Set{Symbol}})
  primary = Dict{Symbol, Symbol}()
  for (k, vs) in pairs(aliases)
    for v in vs 
      primary[v] = k 
    end 
  end 
  primary
end

function Scope(bindings::Vector{Binding{T, Sig}}; 
               aliases=Dict{Symbol, Set{Symbol}}(), 
               tag=newscopetag()) where {T, Sig}
  Scope{T, Sig}(tag, bindings, make_name_dict(bindings), aliases, 
                make_primary_map(aliases))
end

function Scope(pairs::Pair{Symbol, T}...; 
               aliases=Dict{Symbol, Set{Symbol}}(), 
               tag=newscopetag()) where {T}
  Scope(
      Binding{T, Nothing}[Binding{T, Nothing}(x, v) for (x, v) in pairs]; aliases, tag)
end

function Scope{T}(pairs::Pair{Symbol, <:T}...; 
                  aliases=Dict{Symbol, Set{Symbol}}(), 
                  tag=newscopetag()) where {T}
  Scope(Binding{T, Nothing}[Binding{T, Nothing}(x, v) for (x, v) in pairs]; aliases, tag)
end

function Scope(symbols::Symbol...; aliases=Dict{Symbol, Set{Symbol}}(), tag=newscopetag())
  Scope(Pair{Symbol, Nothing}[x => nothing for x in symbols]...; aliases, tag)
end

retag(replacements::Dict{ScopeTag,ScopeTag}, s::Scope{T,Sig}) where {T,Sig} =
  Scope{T,Sig}(get(replacements, gettag(s), gettag(s)), 
               retag.(Ref(replacements), s.bindings), 
               s.names, s.aliases, s.primary)

function Base.show(io::IO, s::Scope)
  n = length(s.bindings) + length(s.primary)
  print(io, "{")
  for (i, b) in enumerate(s.bindings)
    print(io, ScopedBinding(gettag(s), b))
    if i < n
      print(io, ", ")
    end
  end
  for (i, (alias, name)) in enumerate(sort(collect(pairs(s.primary))))
    print(io, "$alias = $name")
    if i + length(s.bindings) < n
      print(io, ", ")
    end
  end
  print(io, "}")
end

getscope(s::Scope) = s

# These functions should only be used when constructing a scope; once a scope
# has been built it should not be mutated.
#
# Thus, these functions are not exported, and must be explicitly imported to be
# used.

"""
Add a new binding to the end of Scope `s`.
"""
function unsafe_pushbinding!(s::Scope{T, Sig}, b::Binding{T,Sig}) where {T, Sig}
  if haskey(s.primary, nameof(b))
    b = setname(b, s.primary[nameof(b)])
  end
  name = nameof(b)
  if !isnothing(name)
    if !haskey(s.names, name)
      s.names[name] = Dict{Sig, LID}()
    end
    if !haskey(s.aliases, name)
      s.aliases[name] = Set{Symbol}()
    end
    sig = getsignature(b)
    if haskey(s.names[name], sig)
      error("name $name already defined with signature $sig in scope $s")
    end
    s.names[name][sig] = LID(length(s.bindings) + 1)
  end
  push!(s.bindings, b)
  b
end

"""
Adds a new alias to the name `x`. This works even if no binding with the name `x`
has been added yet; when a binding is added with name `x`, it will have this alias.
"""
function unsafe_addalias!(s::Scope, name::Symbol, alias::Symbol)
  !haskey(s.names, alias) ||
    error("cannot add $alias as an alias for $name: $alias is already a primary name in $s")
  if haskey(s.primary, name)
    name = s.primary[name]
  end
  if !haskey(s.aliases, name)
    s.aliases[name] = Set{Symbol}()
  end
  s.primary[alias] = name
  push!(s.aliases[name], alias)
end

# HasScope utilities
####################

gettag(hs::HasScope) = getscope(hs).tag

haslid(hs::HasScope, lid::LID) = lid.val ∈ eachindex(getbindings(hs))

function normalize_name(hs::HasScope, name::Symbol)
  s = getscope(hs)
  haskey(s.names, name) ? name : (haskey(s.primary, name) ? s.primary[name] : nothing)
end

function hasname(hs::HasScope, name::Symbol, lid::LID)
  s = getscope(hs)
  name = normalize_name(s, name)
  !(isnothing(name)) && lid ∈ values(s.names[name])
end

hasident(hs::HasScope, x::Ident) =
  gettag(hs) == gettag(x) &&
  haslid(hs, getlid(x)) &&
  (isnothing(nameof(x)) || hasname(hs, nameof(x), getlid(x)))

"""
Determine the level of a binding given the name and possibly the signature
"""
function getlid(
  hs::HasScope{T, Sig}, name::Symbol;
  sig::Union{Sig, Nothing}=nothing,
  isunique::Bool=false
) where {T,Sig}
  s = getscope(hs)
  name = normalize_name(s, name)
  if !isnothing(name) 
    if sig ∈ keys(s.names[name])
      return s.names[name][sig]
    elseif isunique && length(s.names[name]) == 1
      return only(values(s.names[name]))
    end
  end
  throw(KeyError((name, sig)))
end

function getlid(
  hs::HasScope;
  tag::Union{ScopeTag, Nothing}=nothing,
  name::Union{Symbol, Nothing}=nothing,
  lid::Union{LID, Nothing}=nothing,
  level::Union{Int, Nothing}=nothing,
  sig::Any=nothing,
  isunique::Bool=false,
)
  s = getscope(hs)
  isnothing(level) || level == 1 || throw(BoundsError(level, hs))
  isnothing(tag) || tag == gettag(s) || throw(ScopeTagError(hs, tag))
  if isnothing(lid)
    if !isnothing(name)
      getlid(s, name; sig, isunique)
    end
  else
    if haslid(hs, lid)
      lid
    else
      throw(KeyError(lid))
    end
  end
end

getbindings(hs::HasScope) = getscope(hs).bindings

getbinding(hs::HasScope, lid::LID) =
  if haslid(hs, lid)
    getbindings(hs)[lid.val]
  else
    throw(KeyError(lid))
  end

getbinding(hs::HasScope, x::Ident) =
  if hasident(hs, x)
    getbinding(hs, getlid(x))
  else
    throw(ScopeTagError(hs, x))
  end

  getbinding(hs::HasScope, name::Symbol) = getbinding(hs, getlid(hs, name; isunique=true))
  getbinding(hs::HasScope, xs::AbstractVector) = getbinding.(Ref(hs), xs)

function ident(
  hs::HasScope;
  tag::Union{ScopeTag, Nothing}=nothing,
  name::Union{Symbol, Nothing}=nothing,
  lid::Union{LID, Nothing}=nothing,
  level::Union{Int, Nothing}=nothing,
  sig::Any=nothing,
  isunique::Bool=false,
)
  lid = getlid(hs; tag, name, lid, level, sig, isunique)
  binding = getbinding(hs, lid)
  if !isnothing(name)
    return Ident(gettag(hs), lid, name)
  else
    return Ident(gettag(hs), lid, nameof(binding))
  end
end

function identvalues(hs::HasScope)
  map(enumerate(getbindings(hs))) do (i, binding)
    Ident(gettag(hs), LID(i), nameof(binding)) => getvalue(binding)
  end
end

"""This collects all the idents in a scope"""
function getidents(hs::HasScope)
  map(enumerate(getbindings(hs))) do (i, binding)
    Ident(gettag(hs), LID(i), nameof(binding))
  end
end

function namevalues(hs::HasScope)
  map(getbindings(hs)) do binding
    nameof(binding) => getvalue(binding)
  end
end

function Base.values(hs::HasScope)
  map(getbindings(hs)) do binding
    getvalue(binding)
  end
end

Base.valtype(::HasScope{T}) where {T} = T
sigtype(::HasScope{T, Sig}) where {T, Sig} = Sig

# Overloads of methods in Base

Base.length(hs::HasScope) = length(getbindings(hs))

Base.getindex(hs::HasScope, x) = getbinding(hs, x)

# disambiguate method dispatch
Base.getindex(hs::HasScope, x::Ident) = getbinding(hs, x)

Base.iterate(hs::HasScope) = iterate(getbindings(hs))

Base.iterate(hs::HasScope, state) = iterate(getbindings(hs), state)

Base.haskey(hs::HasScope, lid::LID) = haslid(hs, lid)

Base.haskey(hs::HasScope, name::Symbol) = hasname(hs, name)

Base.haskey(hs::HasScope, x::Ident) = hasident(hs, x)

# Context utilities
###################

getscope(c::Context, tag::ScopeTag) = getscope(c, getlevel(c, tag))

getscope(c::Context, x::Ident) = getscope(c, gettag(x))

function hasident(c::Context, x::Ident)
  tag = gettag(x)
  if hastag(c, tag)
    hasident(getscope(c, tag), x)
  else
    false
  end
end

function Base.in(x::Ident, s::Context)
  hasident(s, x)
end

function canonicalize(c::Context, x::Ident)
  ident(c; level=getlevel(c, gettag(x)), lid=getlid(x))
end

"""
`ident` creates an `Ident` from a context and some partial data supplied as keywords.

Keywords arguments:
- `tag::Union{ScopeTag, Nothing}`. The tag of the scope that the `Ident` is in.
- `name::Union{Symbol, Nothing}`. The name of the identifier.
- `lid::Union{LID, Nothing}`. The lid of the identifier within its scope.
- `level::Union{Int, Nothing}`. The level of the scope within the context.
- `sig::Any`. The signature of the identifier, to disambiguate between multiple
  identifiers with the same name within the same scope.
- `strict::Bool`. If `strict` is true, throw an error if not found, else return nothing.
- `isunique::Bool`. If `isunique` is true, then don't use the signature to disambiguate,
  instead fail if their are multiple identifiers with the same name in a scope.
"""
function ident(
  c::Context;
  tag::Union{ScopeTag, Nothing}=nothing,
  name::Union{Symbol, Nothing}=nothing,
  lid::Union{LID, Nothing}=nothing,
  level::Union{Int, Nothing}=nothing,
  sig::Any=nothing,
  isunique::Bool=false,
)
  if isnothing(level)
    if !isnothing(tag)
      if hastag(c, tag)
        level = getlevel(c, tag)
      else
        throw(ScopeTagError(c, tag))
      end
    elseif !isnothing(name)
      if hasname(c, name)
        level = getlevel(c, name)
      else
        throw(KeyError(name))
      end
    end
  end
  if !isnothing(level)
    return ident(getscope(c, level); tag, name, lid, sig, isunique)
  else
    error(
      "insufficient information provided to determine the scope for building an identifier:" *
      "$((;tag, name, lid, level, sig))"
    )
  end
end

"""
`hasident` checks whether an identifier with specified data exists, by
attempting to create it and returning whether or not that attempt failed.
"""
function hasident(c::Context; kwargs...)
  try
    ident(c; kwargs...)
    true
  catch e
    false
  end
end

"""This is a broadcasted version of `ident`"""
function idents(
  c::Context;
  tag=Ref(nothing),
  name=Ref(nothing),
  lid=Ref(nothing),
  level=Ref(nothing),
  sig=Ref(nothing),
  isunique=Ref(false),
)
  broadcast(
    (tag, name, lid, level, sig, isunique) -> ident(c; tag, name, lid, level, sig, isunique),
    tag, name, lid, level, sig, isunique
  )
end

Base.getindex(c::Context, x::Ident) = getbinding(getscope(c, x), x)

getvalue(c::Context, x::Ident) = getvalue(c[x])
getvalue(c::Context, name::Symbol) = getvalue(c[ident(c; name)])

# ScopeList
###########

"""
A type for things which contain a scope list.

Notably, GATs contain a scope list.

Must implement:

`getscopelist(hsl::HasScopeList) -> ScopeList`
"""
abstract type HasScopeList{T, Sig} <: Context{T, Sig} end

struct ScopeList{T, Sig} <: HasScopeList{T, Sig}
  scopes::Vector{HasScope{T,Sig}}
  taglookup::Dict{ScopeTag, Int}
  namelookup::Dict{Symbol, Int}
  function ScopeList(scopes::Vector{<:HasScope{T,Sig}}) where {T,Sig}
    allunique(gettag.(scopes)) || error("tags of scopes in ScopeList must all be unique")
    taglookup = Dict{ScopeTag, Int}()
    namelookup = Dict{Symbol, Int}()
    for (i, hs) in enumerate(scopes)
      s = getscope(hs)
      taglookup[gettag(s)] = i
      for name in keys(s.names)
        namelookup[name] = i # overwrite most recent
      end
      for alias in keys(s.primary)
        namelookup[alias] = i
      end
    end
    new{T, Sig}(scopes, taglookup, namelookup)
  end
end

getscopelist(c::ScopeList) = c

Base.collect(c::ScopeList) = c.scopes

function Base.show(io::IO, s::ScopeList)
  print(io, "[")
  bkspace = false
  for s in s.scopes
    if !isempty(s)
      print(io, s)
      print(io, ", ")
      bkspace = true
    end
  end
  print(io, (bkspace ? "\b\b" : "") * "]")
end


getscope(hsl::HasScopeList, level::Int) =
  getscopelist(hsl).scopes[level]

nscopes(hsl::HasScopeList) =
  length(getscopelist(hsl).scopes)

getlevel(hsl::HasScopeList, t::ScopeTag) =
  getscopelist(hsl).taglookup[t]

getlevel(hsl::HasScopeList, s::Symbol) =
  getscopelist(hsl).namelookup[s]

hastag(hsl::HasScopeList, t::ScopeTag) =
  haskey(getscopelist(hsl).taglookup, t)

hasname(hsl::HasScopeList, name::Symbol) =
  haskey(getscopelist(hsl).namelookup, name)

getidents(hsl::HasScopeList; kw...) = vcat(getidents.(getscopelist(hsl))...)

"""
Flatten a scopelist if possible. This will fail if any of the bindings shadow 
bindings in earlier scopes.
"""
function flatten(hsl::HasScopeList{T, Sig}) where {T, Sig}
  if nscopes(hsl) == 0
    Scope{T, Sig}() 
  else 
    res = Scope(getbindings(deepcopy(getscope(hsl, 1))))
    newtag = gettag(res)
    retagdict = Dict{ScopeTag, ScopeTag}(gettag(getscope(hsl, 1))=>newtag)
    for i in 2:nscopes(hsl)
      nextscope = getscope(hsl, i)
      retagdict[gettag(nextscope)] = newtag
      nextscope = retag(retagdict, nextscope)
      for b in getbindings(nextscope)
        unsafe_pushbinding!(res, b)
      end
    end
    res
  end
end

flatten(s::Scope) = s

# AppendScope
#############

struct AppendScope{T₁, Sig₁, T₂, Sig₂} <: Context{Union{T₁,T₂}, Union{Sig₁,Sig₂}}
  context::Context{T₁, Sig₁}
  last::Scope{T₂, Sig₂}
  function AppendScope(context::Context{T₁, Sig₁}, last::Scope{T₂, Sig₂}) where {T₁, Sig₁, T₂, Sig₂}
    !hastag(context, gettag(last)) || error("All scopes in context must have unique tags: collision with level $(getlevel(context, gettag(last)))")
    new{T₁, Sig₁, T₂, Sig₂}(context, last)
  end
end
function AppendScope(context::Context{T₁, Sig₁}, last::ScopeList{T₂, Sig₂}) where {T₁, Sig₁, T₂, Sig₂}
  res = context
  for scope in getscope.(Ref(last), 1:nscopes(last))
    res = AppendScope(res, scope)
  end
  res
end
getscope(c::AppendScope, level::Int) =
  if level == nscopes(c)
    c.last
  else
    getscope(c.context, level)
  end

nscopes(c::AppendScope) = nscopes(c.context) + 1

getlevel(c::AppendScope, name::Symbol) =
  if name ∈ keys(c.last.names)
    nscopes(c)
  else 
    getlevel(c.context, name)
  end
  
getlevel(c::AppendScope, tag::ScopeTag) =
  gettag(c.last) == tag ? nscopes(c) : getlevel(c.context, tag)

hasname(c::AppendScope, name::Symbol) =
  hasname(c.last, name) || hasname(c.context, name)

hastag(c::AppendScope, tag::ScopeTag) =
  hastag(c.last, tag) || hastag(c.context, tag)

getidents(scope::AppendScope; kw...) = 
  vcat(getidents(scope.context; kw...), getidents(scope.last; kw...))


# EmptyContext
##############

struct EmptyContext{T, Sig} <: Context{T, Sig}
end

getscope(c::EmptyContext, level::Int) = throw(BoundsError(c, level))

nscopes(::EmptyContext) = 0

getlevel(::EmptyContext, name::Symbol) = throw(KeyError(name))

getlevel(::EmptyContext, tag::ScopeTag) = throw(KeyError(tag))

hasname(::EmptyContext, name::Symbol) = false

hastag(::EmptyContext, tag::ScopeTag) = false

end # module
