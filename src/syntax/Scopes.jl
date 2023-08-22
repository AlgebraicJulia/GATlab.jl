module Scopes
export
  ScopeTag, newscopetag, retag, rename,
  Ident, tagof, levelof,
  Path, firstof, restof,
  NamedElt, aliasesof, valueof, signatureof,
  Scope, namesof,
  ScopeTagMismatch

using UUIDs
using MLStyle
using StructEquality

"""
Design rationale:

Namespacing should be first class. This doesn't play nicely with deBruijn
levels; we don't want to do a bunch of math to convert between flattened and
unflattened versions of contexts. There is an accepted solution to the problem
of organizing names: use paths! Mathematically speaking, a path is just a list
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

retag(_replacements::Dict{ScopeTag, ScopeTag}, x) = x
rename(_tag::ScopeTag, _replacements::Dict{Symbol, Symbol}, x) = x

"""
   Ident
An identifier.

`tag` refers to the scope that this Ident is bound in
`level` indexes the scope that Ident is bound in
`name` is an optional field for the sake of printing. A variable in a scope
might be associated with several names
"""
@struct_hash_equal struct Ident
  tag::ScopeTag
  level::Int
  name::Union{Symbol, Nothing}
  function Ident(tag::ScopeTag, level::Int, name::Union{Symbol, Nothing})
    new(tag, level, name)
  end
end

tagof(x::Ident) = x.tag

levelof(x::Ident) = x.level

Base.nameof(x::Ident) = x.name

isnamed(x::Ident) = !isnothing(nameof(x))

function Base.show(io::IO, x::Ident)
  if isnamed(x)
    print(io, nameof(x))
  else
    print(io, "#$(levelof(x))")
  end
end

retag(replacements::Dict{ScopeTag, ScopeTag}, x::Ident) =
  if tagof(x) ∈ keys(replacements)
    Ident(replacements[tagof(x)], levelof(x), nameof(x))
  else
    x
  end

rename(tag::ScopeTag, replacements::Dict{Symbol, Symbol}, x::Ident) =
  if tagof(x) == tag && nameof(x) ∈ keys(replacements)
    Ident(tag, levelof(x), replacements[nameof(x)])
  else
    x
  end

"""
A path of identifiers. We optimize for the (frequent) case where there is only
one identifier by making this a linked list.
"""
@struct_hash_equal struct Path
  first::Ident
  rest::Union{Path, Nothing}
  function Path(first::Ident, rest::Union{Path, Nothing}=nothing)
    new(first, rest)
  end
end

firstof(p::Path) = p.first
restof(p::Path) = p.rest

function Base.show(io::IO, p::Path)
  cur = p
  show(io, cur.first)
  while !isnothing(restof(cur))
    cur = restof(cur)
    id = firstof(cur)
    if isnamed(id)
      print(io, ".")
      show(io, id)
    else
      print(io, "[")
      print(io, levelof(id))
      print(io, "]")
    end
  end
end

retag(replacements::Dict{ScopeTag, ScopeTag}, p::Path) =
  Path(retag(replacements, firstof(p)), retag(replacements, restof(p)))

rename(tag::ScopeTag, replacements::Dict{Symbol, Symbol}, p::Path) =
  Path(rename(tag, replacements, firstof(p)), rename(tag, replacements, restof(p)))

"""
A NamedElement

`primary` is an optional distinguished element of aliases
`value` is the element
`sig` is a way of uniquely distinguishing this element from others with the same name 
(for example, ⊗ : Ob x Ob -> Ob and Hom x Hom -> Hom)
"""
@struct_hash_equal struct NamedElt{T, Sig}
  primary::Union{Symbol, Nothing}
  aliases::Set{Symbol}
  value::T
  sig::Sig
  function NamedElt{T, Sig}(
    primary::Union{Symbol, Nothing},
    aliases::Set{Symbol},
    value::T,
    sig::Sig=nothing,
  ) where {T, Sig}
    isnothing(primary) || primary ∈ aliases ||
      error("if the primary is not nothing then it must be contained in aliases")
    !isnothing(primary) || isempty(aliases) ||
      error("if aliases is nonempty, the primary must be set")
    new{T, Sig}(primary, aliases, value, sig)
  end
  function NamedElt{T}(
    primary::Union{Symbol, Nothing},
    aliases::Set{Symbol},
    value::T,
    sig::Sig=nothing,
  ) where {T, Sig}
    NamedElt{T,Sig}(primary, aliases, value, sig)
  end
end

Base.nameof(ne::NamedElt) = ne.primary
valueof(ne::NamedElt) = ne.value
aliasesof(ne::NamedElt) = ne.aliases
signatureof(ne::NamedElt) = ne.sig

retag(replacements::Dict{ScopeTag, ScopeTag}, elt::NamedElt{T, Sig}) where {T, Sig} =
  NamedElt{T,Sig}(
    nameof(elt),
    aliasesof(elt),
    retag(replacements, valueof(elt)),
    retag(replacements, signatureof(elt))
  )

function make_name_dict(elts::AbstractVector{NamedElt{T, Sig}}) where {T, Sig}
  d = Dict{Symbol, Dict{Sig, Int}}()
  for (i, elt) in enumerate(elts)
    for name in aliasesof(elt)
      if !(name ∈ keys(d))
        d[name] = Dict{Sig, Int}()
      end
      sig = signatureof(elt)
      if sig ∈ keys(d[name])
        error("already defined $name with signature $sig")
      end
      d[name][sig] = i
    end
  end
  d
end

struct Scope{T, Sig}
  tag::ScopeTag
  elts::Vector{NamedElt{T, Sig}}
  names::Dict{Symbol, Dict{Sig, Int}}
end

function Scope(named_elts::Vector{NamedElt{T, Sig}}; tag=newscopetag()) where {T, Sig}
  Scope{T, Sig}(tag, named_elts, make_name_dict(named_elts))
end

tagof(s::Scope) = s.tag
namesof(s::Scope) = s.names

struct ScopeTagMismatch <: Exception
  id::Ident
  expectedcontext::Any
end

Base.showerror(io::IO, e::ScopeTagMismatch) =
  print(io, "tag from ", id, " does not match ", e.expectedcontext)

function Base.getindex(s::Scope, id::Ident)
  tagof(id) == tagof(s) || throw(ScopeTagMismatch(id, s))
  s.elts[levelof(id)].value
end

function Base.getindex(s::Scope, path::Path)
  x = s[firstof(path)]
  if !isnothing(restof(path))
    x[restof(path)]
  else
    x
  end
end

end # module
