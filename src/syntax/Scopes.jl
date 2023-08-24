module Scopes
export
  ScopeTag, newscopetag, retag, rename,
  ScopeTagError,
  Ident, gettag, getlevel, isnamed,
  Reference, rest,
  Binding, getaliases, getvalue, getsignature, getline, setline,
  Scope, ident, idents,
  Context, scopelevel,
  ScopeList, AppendScope

using UUIDs
using MLStyle
using StructEquality
import Base: rest

"""
Design rationale:

Namespacing should be first class. This doesn't play nicely with deBruijn
levels; we don't want to do a bunch of math to convert between flattened and
unflattened versions of contexts. There is an accepted solution to the problem
of organizing names: use refs! Mathematically speaking, a ref is just a list
of deBruijn levels.

However, deBruijn levels are unfriendly for users; we want to be able to give
names to our variables!

In general, naming is given by a *relation* between symbols and bindings (as
referred to by deBruijn levels). Each binding may be associated with zero or
more symbols, and each symbol might be associated with zero or more bindings.

We name the failure of this relation to be a bijection in several ways.

- If more than one symbol is related to a single binding, we say that this
binding has *aliases*. In this case, we should also have a *primary alias*
used as a default.
- If more than one binding is related to a single symbol, we have *name overlap*.
Name overlap can be resolved by *overloading* and *shadowing*, we will talk
about this later on.
- If no symbol is related to a binding, such as when the binding is created
programmatically, we need *nameless references* to be able to refer to the
binding, which are also created programmatically.
- If no binding is related to a symbol, then we have a *name error*; this name
is not valid in the current context and we must throw an error.

The most important thing to get right is *name overlap*; we discuss this first.

There are two ways in which to resolve name overlap.  The first way is via
*overloading*. In overloading, we disambiguate an ambiguous name via its
context, for instance what type it is expected to be, or what arguments is it
receiving. The second way is via *shadowing*. In shadowing, a name is resolved
by making it point to the "most recently defined" thing with that name.

In Gatlab, we handle overloading and shadowing with a notion of *scope*.
Anything which binds variables introduces a scope, for instance a `@theory`
declaration or a context. Each scope is identified with a ScopeTag, which is an
opaque identifier (i.e. a UUID). We take this idea from Racket, but we don't
need the more complex "scope sets" from Racket because GATs don't need to
process the syntax of other GATs; if we start doing this we'll have to rethink
the design, but we'll probably have bigger problems too.

Two variables with the same name within a single scope are meant to overload one
another. For instance, this is what happens with `mcompose` in the theory of
monoidal categories; it is overloaded for `Hom` and `Ob`, and this is what
happens with `d` in the discrete exterior calculus; it is overloaded for all of
the (k+1)-forms. Variables in different scopes with the same name *shadow* one
another. When we parse an expression `a + b`, we do so in an ordered list of
scopes, and the most recent scope "wins".

Parsing turns a `Symbol` into an `Ident`. The `Ident` contains the original
`Symbol` for printing, but it also contains a reference to a scope via ScopeTag,
and an deBruijn level within that scope. Thus, the name in the `Ident` is never
needed for later stages of programatic manipulation.

Scopes cache the relation between names and bindings, by providing a way to go
from binding (as reified by deBruijn level) to a set of aliases with
distinguished primary alias, and to go from name to the set of bindings that
have that name that we need to disambiguate between in the case of an overload.

Because `Ident`s are fully unambiguous even without their name, it is also possible
to create an `Ident` with no name, which solves the problem of *nameless references*.
"""

"""
The tag that makes reference to a specific scope possible.
"""
const ScopeTag = UUID
newscopetag() = uuid4()


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
`Ident`

An identifier.

`tag` refers to the scope that this Ident is bound in
`level` indexes the scope that Ident is bound in
`name` is an optional field for the sake of printing. A variable in a scope
might be associated with several names
"""
struct Ident
  tag::ScopeTag
  level::Int
  name::Union{Symbol, Nothing}
  function Ident(tag::ScopeTag, level::Int, name::Union{Symbol, Nothing}=nothing)
    new(tag, level, name)
  end
end

Base.:(==)(x::Ident, y::Ident) = x.tag == y.tag && x.level == y.level

Base.hash(x::Ident, h::UInt64) = hash(x.tag, hash(x.level, h))

gettag(x::Ident) = x.tag

getlevel(x::Ident) = x.level

Base.nameof(x::Ident) = x.name

isnamed(x::Ident) = !isnothing(nameof(x))

function Base.show(io::IO, x::Ident)
  if isnamed(x)
    print(io, nameof(x))
  else
    print(io, "#$(getlevel(x))")
  end
end

retag(replacements::Dict{ScopeTag, ScopeTag}, x::Ident) =
  if gettag(x) ∈ keys(replacements)
    Ident(replacements[gettag(x)], getlevel(x), nameof(x))
  else
    x
  end

rename(tag::ScopeTag, replacements::Dict{Symbol, Symbol}, x::Ident) =
  if gettag(x) == tag && nameof(x) ∈ keys(replacements)
    Ident(tag, getlevel(x), replacements[nameof(x)])
  else
    x
  end

"""
`ScopeTagError`

An error to throw when an identifier has an unexpected scope tag
"""
struct ScopeTagError <: Exception
  expectedcontext::Any
  id::Ident
end

Base.showerror(io::IO, e::ScopeTagError) =
  print(io, "tag from ", e.id, " does not match ", e.expectedcontext)

"""
`Reference`

A path of identifiers. We optimize for the (frequent) case where there is only
one identifier by making this a linked list.
"""
@struct_hash_equal struct Reference
  first::Ident
  rest::Union{Reference, Nothing}
  function Reference(first::Ident, rest::Union{Reference, Nothing}=nothing)
    new(first, rest)
  end
end

function Reference(first::Ident, rest...)
  if isempty(rest)
    Reference(first)
  else
    Reference(first, Reference(rest...))
  end
end

Base.first(p::Reference) = p.first
Base.rest(p::Reference) = p.rest

function Base.show(io::IO, p::Reference)
  cur = p
  show(io, cur.first)
  while !isnothing(rest(cur))
    cur = rest(cur)
    id = first(cur)
    if isnamed(id)
      print(io, ".")
      show(io, id)
    else
      print(io, "[")
      print(io, getlevel(id))
      print(io, "]")
    end
  end
end

retag(replacements::Dict{ScopeTag, ScopeTag}, p::Reference) =
  Reference(retag(replacements, first(p)), retag(replacements, rest(p)))

rename(tag::ScopeTag, replacements::Dict{Symbol, Symbol}, p::Reference) =
  Reference(rename(tag, replacements, first(p)), rename(tag, replacements, rest(p)))

"""
`Binding{T, Sig}`

`primary` is an optional distinguished element of aliases
`value` is the element
`sig` is a way of uniquely distinguishing this element from others with the same name 
(for example, ⊗ : Ob x Ob -> Ob and Hom x Hom -> Hom)
"""
@struct_hash_equal struct Binding{T, Sig}
  primary::Union{Symbol, Nothing}
  aliases::Set{Symbol}
  value::T
  sig::Sig
  line::Union{LineNumberNode, Nothing}
  function Binding{T, Sig}(
    primary::Union{Symbol, Nothing},
    aliases::Set{Symbol},
    value::T,
    sig::Sig=nothing,
    line::Union{LineNumberNode, Nothing}=nothing
  ) where {T, Sig}
    isnothing(primary) || primary ∈ aliases ||
      error("if the primary is not nothing then it must be contained in aliases")
    !isnothing(primary) || isempty(aliases) ||
      error("if aliases is nonempty, the primary must be set")
    new{T, Sig}(primary, aliases, value, sig, line)
  end
  function Binding{T}(
    primary::Union{Symbol, Nothing},
    aliases::Set{Symbol},
    value::T,
    sig::Sig=nothing,
    line::Union{LineNumberNode, Nothing}=nothing
  ) where {T, Sig}
    Binding{T,Sig}(primary, aliases, value, sig, line)
  end
end

function Base.show(io::IO, b::Binding)
  print(io, isnothing(nameof(b)) ? "_" : nameof(b))
  if length(getaliases(b)) > 1 
    print(io, "(aliases=")
    join(io, filter(x -> x != nameof(b), getaliases(b)), ", ")
    print(io,")")
  end
  print(io, isnothing(getsignature(b)) ? "" : "::$getsignature(b)")
  print(io, " => $(repr(getvalue(b)))")
end


Base.nameof(ne::Binding) = ne.primary

getvalue(ne::Binding) = ne.value

getaliases(ne::Binding) = ne.aliases

getsignature(ne::Binding) = ne.sig

retag(replacements::Dict{ScopeTag, ScopeTag}, binding::Binding{T, Sig}) where {T, Sig} =
  Binding{T,Sig}(
    nameof(binding),
    getaliases(binding),
    retag(replacements, getvalue(binding)),
    retag(replacements, getsignature(binding))
  )

getline(b::Binding) = b.line

setline(b::Binding{T, Sig}, line::Union{LineNumberNode, Nothing}) where {T, Sig} =
  Binding{T, Sig}(b.primary, b.aliases, b.value, b.sig, line)

"""
A `Context` is anything which contains an ordered list of scopes.

`Context`s should overload:

- `ident`
- `Base.getindex(c::Context, x::Ident) -> Binding`
- `Base.getindex(c::Context, i::Int) -> Scope`
- `scopelevel(c::Context, name::Symbol) -> Union{Int, Nothing}`
- `scopelevel(c::Context, tag::ScopeTag) -> Union{Int, Nothing}`
- `Base.length`
- `Base.contains(c::Context, tag::ScopeTag) -> Bool`
"""
abstract type Context end

"""
`ident(c::Context, name::Symbol; sig=nothing, scopelevel=nothing) -> Ident`

`ident(c::Context, level::Int; scopelevel=nothing) -> Ident`
"""
function ident end 

Base.lastindex(c::Context) = length(c)
Base.collect(c::Context) = [c[i] for i in 1:length(c)]

function make_name_dict(bindings::AbstractVector{Binding{T, Sig}}) where {T, Sig}
  d = Dict{Symbol, Dict{Sig, Int}}()
  for (i, binding) in enumerate(bindings)
    for name in getaliases(binding)
      if !(name ∈ keys(d))
        d[name] = Dict{Sig, Int}()
      end
      sig = getsignature(binding)
      if sig ∈ keys(d[name])
        error("already defined $name with signature $sig")
      end
      d[name][sig] = i
    end
  end
  d
end

"""
`Scope{T, Sig}`

In Gatlab, we handle overloading and shadowing with a notion of *scope*.
Anything which binds variables introduces a scope, for instance a `@theory`
declaration or a context. For example, a scope with 3 elements:

x::Int = 3
y::String = "hello"
x::String = "ex"

This is a valid scope even though there are name collisions, because the 
signature (in this case, a datatype) disambiguates. In this case, `namesof(scope)` 
would return:

  `Dict(x => Dict(Int => 3, String => "ex), y => Dict(String => "hello"))`
"""
struct Scope{T, Sig}
  # unique identifier for the scope
  tag::ScopeTag
  # ordered sequence of name assignments
  bindings::Vector{Binding{T, Sig}}
  # a cached mapping which takes a name and a disambiguator (i.e. signature)
  # and returns the index in `bindings`
  names::Dict{Symbol, Dict{Sig, Int}}
end

Scope{T, Sig}() where {T, Sig} = Scope{T, Sig}(newscopetag(), Binding{T, Sig}[], Dict{Symbol, Dict{Sig, Int}}())

function Scope(bindings::Vector{Binding{T, Sig}}; tag=newscopetag()) where {T, Sig}
  Scope{T, Sig}(tag, bindings, make_name_dict(bindings))
end

function Base.show(io::IO, x::Scope)
  print(io, "{")
  for (i, b) in enumerate(x.bindings)
    print(io, b)
    if i < length(x.bindings)
      print(io, ", ")
    end
  end
  print(io, "}")
end

gettag(s::Scope) = s.tag

getlevel(s::Scope{T,Sig}, name::Symbol, sig::Sig) where {T,Sig} =
  s.names[name][sig]

getlevel(s::Scope{T, Nothing}, name::Symbol) where {T} =
  s.names[name][nothing]

function getlevel(s::Scope, x::Ident)
  gettag(s) == gettag(x) || throw(ScopeTagError(s, x))
  getlevel(s, getlevel(x))
end

function getlevel(s::Scope, level::Int)
  level ∈ eachindex(s.bindings) || BoundsError(s, level)
  level
end

Base.getindex(s::Scope, x) = s.bindings[getlevel(s, x)]

Base.getindex(s::Scope, name::Symbol, sig) = s.bindings[getlevel(s, name, sig)]

function Base.getindex(s::Scope, ref::Reference)
  x = s[first(ref)]
  if !isnothing(rest(ref))
    getvalue(x)[rest(ref)]
  else
    x
  end
end

Base.iterate(s::Scope) = iterate(s.bindings)
Base.iterate(s::Scope, i) = iterate(s.bindings, i)

Base.length(s::Scope) = length(s.bindings)

function Base.push!(s::Scope{T, Sig}, b::Binding{T,Sig}) where {T, Sig}
  sig = getsignature(b)
  for name in getaliases(b)
    if name ∈ keys(s.names) && sig ∈ keys(s.names[name])
      error("$name already bound with signature $sig in $s")
    end
    if name ∉ keys(s.names)
      s.names[name] = Dict{Sig, Int}()
    end
    s.names[name][sig] = length(s.bindings) + 1
  end
  push!(s.bindings, b)
end

ident(s::Scope, name::Symbol; sig=nothing) =
  Ident(gettag(s), getlevel(s, name, sig), name)

function ident(s::Scope, level::Int, name=nothing)
  binding = s.bindings[level]
  isnothing(name) || name ∈ binding.aliases || error("invalid alias $name for $binding")
  Ident(gettag(s), level, isnothing(name) ? nameof(binding) : name)
end

idents(s::Scope, names::AbstractVector{Symbol}) = ident.(Ref(s), names)

idents(s::Scope{T, Sig}, names::AbstractVector{Symbol}, sigs::AbstractVector{Int}) where {T, Sig} =
  ident.(Ref(s), names, sigs)

idents(s::Scope{T, Sig}, pairs::AbstractVector{Tuple{Symbol, Sig}}) where {T, Sig} =
  idents(s, first.(paris), second.(pairs))

idents(s::Scope, levels::AbstractVector{Int}) = ident.(Ref(s), levels)

idents(s::Scope, levels::AbstractVector{Int}, names::AbstractVector{Symbol}) =
  ident.(Ref(s), levels, names)

idents(s::Scope, pairs::AbstractVector{Tuple{Int, Symbol}}) =
  idents(s, first.(pairs), second.(pairs))
  

struct ScopeList <: Context
  scopes::Vector{Scope}
  taglookup::Dict{ScopeTag, Int}
  namelookup::Dict{Symbol, Int}
  function ScopeList(scopes::Vector{<:Scope}=Scope[])
    taglookup = Dict{ScopeTag, Int}()
    namelookup = Dict{Symbol, Int}()
    for (i, s) in enumerate(scopes)
      taglookup[gettag(s)] = i
      for binding in s
        for alias in getaliases(binding)
          namelookup[alias] = i # overwrite most recent
        end
      end 
    end
    new(Vector{Scope}(scopes), taglookup, namelookup)
  end
end

getscopes(c::ScopeList) = c.scopes

scopelevel(c::ScopeList, t::ScopeTag) = c.taglookup[t]
scopelevel(c::ScopeList, s::Symbol) = c.namelookup[s]

Base.length(c::ScopeList) = length(c.scopes)
Base.getindex(c::ScopeList, x::Ident) = c[scopelevel(c, gettag(x))][x]
Base.getindex(c::ScopeList, i::Int) = getscopes(c)[i]

function ident(c::ScopeList, level::Int; name=nothing, scopelevel::Union{Int, Nothing}=nothing)
  scope = isnothing(scopelevel) ? c[end] : c[scopelevel]
  ident(scope, level; name)
end

function ident(c::ScopeList, name::Symbol; sig=nothing, scopelevel::Union{Int, Nothing}=nothing)
  scope = c[isnothing(scopelevel) ? c.namelookup[name] : scopelevel]
  ident(scope, name; sig)
end

struct AppendScope <: Context
  context::Context
  last::Scope
end

Base.length(c::AppendScope) = length(c.context) + 1
Base.getindex(c::AppendScope, i::Int) = i == length(c) ? c.last : c.context[i]
Base.getindex(c::AppendScope, x::Ident) = gettag(i) == gettag(c.last) ? c.last[x] : c.context[x]

function ident(c::AppendScope, name::Symbol; sig=nothing, scopelevel::Union{Int, Nothing}=nothing)
  if !isnothing(scopelevel)
    if scopelevel == length(c)
      ident(c.last, name; sig)
    else
      ident(c.context, name; sig, scopelevel)
    end
  else
    if name ∈ keys(c.last.names)
      ident(c.last, name; sig)
    else
      ident(c.context, name; sig)
    end
  end
end

function ident(c::AppendScope, level::Int; name=nothing, scopelevel::Union{Int, Nothing}=nothing)
  if scopelevel == length(c)
    ident(c.last, level; name)
  else 
    ident(c.context, level; name, scopelevel)
  end 
end

scopelevel(c::AppendScope, name::Symbol) = 
  if name ∈ keys(c.last.names)
    length(c)
  else 
    scopelevel(c.context, name)
  end
  
scopelevel(c::AppendScope, tag::ScopeTag) = gettag(c.last) == tag ? length(c) : scopelevel(c.context, tag)
Base.contains(c::AppendScope, tag::ScopeTag) = gettag(c.last) == tag || tag ∈ c

end # module
