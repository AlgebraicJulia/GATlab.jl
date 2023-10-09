module Scopes
export
  ScopeTag, newscopetag, retag, rename,
  ScopeTagError,
  LID,
  Ident, Alias, gettag, getlid, isnamed,
  Binding, getvalue, setvalue, getline, setline,
  Context, getscope, nscopes, getlevel, hasname, hastag, alltags, allscopes,
  HasContext, getcontext,
  hasident, ident, getidents, idents, canonicalize,
  HasScope, haslid, getscope, getbindings, getbinding,
  identvalues, namevalues,
  Scope, ScopeList, HasScopeList, AppendContext,
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

@struct_hash_equal struct Alias 
  ref::Ident 
end

"""
`Binding{T}`

A binding associates some `T`-typed value to a name.

`name` is an optional distinguished name
`value` is the element
"""
@struct_hash_equal struct Binding{T}
  name::Union{Symbol, Nothing}
  value::Union{T, Alias}
  line::Union{LineNumberNode, Nothing}
  function Binding{T}(
    name::Union{Symbol, Nothing},
    value::Union{T, Alias},
    line::Union{LineNumberNode, Nothing}=nothing
  ) where {T}
    new{T}(name, value, line)  
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
  value = getvalue(b)
  if value isa Alias
    print(io, " = ", value.ref)
  else
    print(io, " => $(repr(getvalue(b)))")
  end
end

Base.nameof(b::Binding) = b.name

function MetaUtils.setname(b::Binding{T}, name::Symbol) where {T}
  Binding{T}(name, b.value, b.line)
end

getvalue(b::Binding) = b.value

retag(replacements::Dict{ScopeTag, ScopeTag}, binding::Binding{T}) where {T} =
  Binding{T}(
    nameof(binding),
    retag(replacements, getvalue(binding)),
  )

getline(b::Binding) = b.line

setline(b::Binding{T}, line::Union{LineNumberNode, Nothing}) where {T} =
  Binding{T}(b.name, b.value, line)

setvalue(b::Binding{T}, t::T) where {T} = 
  Binding{T}(b.name, t, b.line)

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
- `alltags(c::Context) -> Set{ScopeTag}`
"""
abstract type Context{T} end

abstract type HasContext{T} <: Context{T} end

function getcontext end

getscope(hc::HasContext, level::Int) = getscope(getcontext(hc), level)

nscopes(hc::HasContext) = nscopes(getcontext(hc))

hastag(hc::HasContext, tag::ScopeTag) = hastag(getcontext(hc), tag)

hasname(hc::HasContext, name::Symbol) = hasname(getcontext(hc), name)

getlevel(hc::HasContext, tag::ScopeTag) = getlevel(getcontext(hc), tag)

getlevel(hc::HasContext, name::Symbol) = getlevel(getcontext(hc), name)

alltags(hc::HasContext) = alltags(getcontext(hc))

# HasScope
##########

"""
An abstract type for wrappers around a single scope.

Must overload

`getscope(hs::HasScope) -> Scope`
"""
abstract type HasScope{T} <: Context{T} end

getscope(hs::HasScope, x::Int) =
  x == 1 ? getscope(hs) : throw(BoundsError(hs, x))

hastag(hs::HasScope, tag::ScopeTag) = getscope(hs).tag == tag

hasname(hs::HasScope, name::Symbol) = haskey(getscope(hs).names, name)

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

alltags(hs::HasScope) = Set([getscope(hs).tag])

# Scopes
########

"""
`Scope{T}`

In GATlab, we handle shadowing with a notion of *scope*.
Names shadow between scopes.
Anything which binds variables introduces a scope, for instance a `@theory`
declaration or a context. For example, here is a scope with 3 elements:

```
x = 3
y = "hello"
z = x 
```

Here z is introduced as an alias for x. It is illegal to shadow within a scope.
Overloading is not explicitly treated but can be managed by having values which 
refer to identifiers earlier / the present scope. See GATs.jl, for example.
"""
struct Scope{T} <: HasScope{T}
  # unique identifier for the scope
  tag::ScopeTag
  # ordered sequence of name assignments
  bindings::Vector{Binding{T}}
  # cached mapping
  names::Dict{Symbol, LID}
  function Scope{T}(tag, bindings, names) where {T}
    new{T}(tag, bindings, names)
  end
end

Base.:(==)(s1::Scope, s2::Scope) = s1.tag == s2.tag

Base.hash(s::Scope, h::UInt64) = hash(s.tag, h)

Scope{T}() where {T} = 
  Scope{T}(newscopetag(), Binding{T}[], Dict{Symbol, LID}())

check_names(s::Scope) = make_name_dict(s.bindings) == s.names

function make_name_dict(bindings::AbstractVector{Binding{T}}) where {T}
  d = Dict{Symbol, LID}()
  for (i, binding) in enumerate(bindings)
    name = nameof(binding)
    if isnothing(name) 
      continue 
    end
    if haskey(d, name)
      error("Scopes do not permit shadowing: binding $binding shadows existing binding $(bindings[d[name].val])")
    end
    d[name] = LID(i)
  end
  d
end

function Scope(bindings::Vector{Binding{T}}; tag=newscopetag()) where {T}
  Scope{T}(tag, bindings, make_name_dict(bindings))
end

function Scope(pairs::Pair{Symbol, T}...; tag=newscopetag()) where {T}
  Scope(Binding{T}[Binding{T}(x, v) for (x, v) in pairs]; tag)
end

function Scope{T}(pairs::Pair{Symbol, <:T}...; tag=newscopetag()) where {T}
  Scope(Binding{T}[Binding{T}(x, v) for (x, v) in pairs]; tag)
end

function Scope(symbols::Symbol...; tag=newscopetag())
  Scope(Pair{Symbol}[x => nothing for x in symbols]...; tag)
end

retag(replacements::Dict{ScopeTag,ScopeTag}, s::Scope{T}) where {T} =
  Scope{T}(
    get(replacements, gettag(s), gettag(s)),
    retag.(Ref(replacements), s.bindings),
    s.names
  )

function Base.show(io::IO, s::Scope)
  n = length(s.bindings)
  print(io, "{")
  for (i, b) in enumerate(s.bindings)
    print(io, ScopedBinding(gettag(s), b))
    if i < n
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
function unsafe_pushbinding!(s::Scope{T}, b::Binding{T}) where {T}
  name = nameof(b)
  if haskey(s.names, nameof(b))
    error("name $name already defined in scope $s")
  end
  if !isnothing(name)
    s.names[name] = LID(length(s.bindings) + 1)
  end
  push!(s.bindings, b)
  Ident(gettag(s), LID(length(s.bindings)), nameof(b))
end

# HasScope utilities
####################

gettag(hs::HasScope) = getscope(hs).tag

haslid(hs::HasScope, lid::LID) = lid.val ∈ eachindex(getbindings(hs))

function hasname(hs::HasScope, name::Symbol, lid::LID)
  s = getscope(hs)
  lid == s.names[name]
end

hasident(hs::HasScope, x::Ident) =
  gettag(hs) == gettag(x) &&
  haslid(hs, getlid(x)) &&
  (isnothing(nameof(x)) || hasname(hs, nameof(x), getlid(x)))

"""
Determine the level of a binding given the name
"""
getlid(hs::HasScope, name::Symbol) = getscope(hs).names[name]

function getlid(
  hs::HasScope;
  tag::Union{ScopeTag, Nothing}=nothing,
  name::Union{Symbol, Nothing}=nothing,
  lid::Union{LID, Nothing}=nothing,
  level::Union{Int, Nothing}=nothing,
)
  s = getscope(hs)
  isnothing(level) || level == 1 || throw(BoundsError(level, hs))
  isnothing(tag) || tag == gettag(s) || throw(ScopeTagError(hs, tag))
  if isnothing(lid)
    if !isnothing(name)
      getlid(s, name)
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

  getbinding(hs::HasScope, name::Symbol) = getbinding(hs, getlid(hs, name))
  getbinding(hs::HasScope, xs::AbstractVector) = getbinding.(Ref(hs), xs)

function ident(
  hs::HasScope;
  tag::Union{ScopeTag, Nothing}=nothing,
  name::Union{Symbol, Nothing}=nothing,
  lid::Union{LID, Nothing}=nothing,
  level::Union{Int, Nothing}=nothing,
)
  lid = getlid(hs; tag, name, lid, level)
  binding = getbinding(hs, lid)
  value = getvalue(binding)
  if value isa Alias
    return value.ref
  end
  if isnothing(name)
    name = nameof(getbinding(hs, lid))
  end
  Ident(gettag(hs), lid, name)
end

function identvalues(hs::HasScope)
  map(enumerate(getbindings(hs))) do (i, binding)
    Ident(gettag(hs), LID(i), nameof(binding)) => getvalue(binding)
  end
end

"""This collects all the idents in a scope"""
function getidents(hs::HasScope; aliases=true)
  xs = Ident[]
  for (i, binding) in enumerate(getbindings(hs))
    if aliases || !(getvalue(binding) isa Alias)
      push!(xs, Ident(gettag(hs), LID(i), nameof(binding)))
    end
  end
  xs
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

allscopes(c::Context) = [getscope(c, i) for i in 1:nscopes(c)]

function Base.in(x::Ident, s::Context)
  hasident(s, x)
end

"""
`ident` creates an `Ident` from a context and some partial data supplied as keywords.

Keywords arguments:
- `tag::Union{ScopeTag, Nothing}`. The tag of the scope that the `Ident` is in.
- `name::Union{Symbol, Nothing}`. The name of the identifier.
- `lid::Union{LID, Nothing}`. The lid of the identifier within its scope.
- `level::Union{Int, Nothing}`. The level of the scope within the context.
- `strict::Bool`. If `strict` is true, throw an error if not found, else return nothing.
"""
function ident(
  c::Context;
  tag::Union{ScopeTag, Nothing}=nothing,
  name::Union{Symbol, Nothing}=nothing,
  lid::Union{LID, Nothing}=nothing,
  level::Union{Int, Nothing}=nothing,
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
    return ident(getscope(c, level); tag, name, lid)
  else
    error(
      "insufficient information provided to determine the scope for building an identifier:" *
      "$((;tag, name, lid, level))"
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
  catch _
    false
  end
end

"""
This is a broadcasted version of `ident`
"""
function idents(
  c::Context;
  tag=Ref(nothing),
  name=Ref(nothing),
  lid=Ref(nothing),
  level=Ref(nothing),
)
  broadcast(
    (tag, name, lid, level) -> ident(c; tag, name, lid, level),
    tag, name, lid, level
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
abstract type HasScopeList{T} <: Context{T} end

struct ScopeList{T} <: HasScopeList{T}
  scopes::Vector{HasScope{T}}
  taglookup::Dict{ScopeTag, Int}
  namelookup::Dict{Symbol, Int}
end

function ScopeList(scopes::Vector{<:HasScope{T}}) where {T}
  ScopeList{T}(scopes)
end
function ScopeList{T}(scopes::Vector{<:HasScope{T}}) where {T}
  allunique(gettag.(scopes)) || error("tags of scopes in ScopeList must all be unique")
  taglookup = Dict{ScopeTag, Int}()
  namelookup = Dict{Symbol, Int}()
  c = ScopeList{T}(scopes, taglookup, namelookup)
  for (i, hs) in enumerate(scopes)
    unsafe_updatecache!(c, i, hs)
  end
  c
end

function Base.copy(c::ScopeList{T}) where {T}
  ScopeList{T}(copy(c.scopes), copy(c.taglookup), copy(c.namelookup))
end

function ScopeList{T}() where {T}
  ScopeList{T}(HasScope{T}[])
end

function unsafe_pushbinding!(c::ScopeList{T}, binding::Binding{T}) where {T}
  name = nameof(binding)
  if !isnothing(name)
    c.namelookup[name] = length(c.scopes)
  end
  unsafe_pushbinding!(getscope(c.scopes[end]), binding)
end

function unsafe_updatecache!(c::ScopeList{T}, i::Int, hs::HasScope{T}) where {T}
  s = getscope(hs)
  c.taglookup[gettag(s)] = i
  for name in keys(s.names)
    c.namelookup[name] = i # overwrite most recent
  end
end

function unsafe_pushscope!(c::ScopeList{T}, scope::HasScope{T}) where {T}
  push!(c.scopes, scope)
  unsafe_updatecache!(c, length(c.scopes), scope)
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
  getscope(getscopelist(hsl).scopes[level])

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

getidents(hsl::HasScopeList; kw...) = vcat(getidents.(getscopelist(hsl); kw...)...)

alltags(hsl::HasScopeList) = Set(gettag.(getscopelist(hsl).scopes))

# AppendContext
###############

struct AppendContext{T₁, T₂} <: Context{Union{T₁,T₂}}
  ctx1::Context{T₁}
  ctx2::Context{T₂}
  function AppendContext(ctx1::Context{T₁}, ctx2::Context{T₂}) where {T₁, T₂}
    isempty(intersect(alltags(ctx1), alltags(ctx2))) ||
      error("All scopes in context must have unique tags")
    new{T₁, T₂}(ctx1, ctx2)
  end
end

getscope(c::AppendContext, level::Int) =
  if level > nscopes(c.ctx1)
    getscope(c.ctx2, level - nscopes(c.ctx1))
  else
    getscope(c.ctx1, level)
  end

nscopes(c::AppendContext) = nscopes(c.ctx1) + nscopes(c.ctx2)

getlevel(c::AppendContext, name::Symbol) =
  if hasname(c.ctx2, name)
    getlevel(c.ctx2, name) + nscopes(c.ctx1)
  else 
    getlevel(c.ctx1, name)
  end
  
getlevel(c::AppendContext, tag::ScopeTag) =
  if hastag(c.ctx2, tag)
    getlevel(c.ctx2, tag) + nscopes(c.ctx1)
  else
    getlevel(c.ctx1, tag)
  end

hasname(c::AppendContext, name::Symbol) =
  hasname(c.ctx2, name) || hasname(c.ctx1, name)

hastag(c::AppendContext, tag::ScopeTag) =
  hastag(c.ctx2, tag) || hastag(c.ctx1, tag)

getidents(c::AppendContext; kw...) =
  vcat(getidents(c.ctx1; kw...), getidents(c.ctx2; kw...))

alltags(c::AppendContext) = union(alltags(c.ctx1), alltags(c.ctx2))

# EmptyContext
##############

struct EmptyContext{T} <: Context{T}
end

getscope(c::EmptyContext, level::Int) = throw(BoundsError(c, level))

nscopes(::EmptyContext) = 0

getlevel(::EmptyContext, name::Symbol) = throw(KeyError(name))

getlevel(::EmptyContext, tag::ScopeTag) = throw(KeyError(tag))

hasname(::EmptyContext, name::Symbol) = false

hastag(::EmptyContext, tag::ScopeTag) = false

alltags(::EmptyContext) = Set{ScopeTag}()

end # module
