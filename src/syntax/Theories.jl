module Theories
export Lvl, Typ, Trm, TypCon, TrmCon, Axiom, Context, Judgment, Theory,
  AbstractTheory, gettheory, empty_theory, ThEmpty, index, is_context, FullContext,
  lookup, arity, judgments, rename, getname

using StructEquality

using ...Util

@struct_hash_equal struct Lvl
  val::UInt64
  function Lvl(i::Integer; context=false)
    i > 0 || error("Creating non-positive level $i context $context")
    new(UInt64(i) | (UInt64(context) << 63))
  end
end

const CONTEXT_BIT = UInt64(1) << 63

is_context(i::Lvl) = (i.val & CONTEXT_BIT) != 0

index(i::Lvl) = i.val & (CONTEXT_BIT - 1)

Base.:(+)(i::Lvl, j::Int) = Lvl(i.val + UInt64(j))

abstract type TrmTyp end 

@struct_hash_equal struct Trm <:TrmTyp
  head::Lvl
  args::Vector{Trm}
  function Trm(l::Lvl,a=Trm[])
    !(is_context(l) && !isempty(a)) || error("Elements of context are *nullary* term constructors")
    return new(l,a)
  end
  function Trm(l::Int,a=Trm[])
    return new(Lvl(l), a)
  end
end

"""
The head of a type can never come from a context, only a theory, because it 
should point at a type constructor judgment.
"""
@struct_hash_equal struct Typ <: TrmTyp
  head::Lvl
  args::Vector{Trm}
  function Typ(l,a=Lvl[]) 
    !is_context(l) || error("Bad head for type: $(index(l))")
    return new(l,a)
  end 
end


@struct_hash_equal struct Context
  ctx::Vector{Tuple{Name, Typ}}
  Context(c=Tuple{Name, Typ}[]) = new(c)
end 

Base.getindex(c::Context,i::Lvl) = is_context(i) ? c.ctx[index(i)] : error("$i")
Base.collect(c::Context) = collect(c.ctx)
Base.length(c::Context) = length(c.ctx)
Base.iterate(c::Context,i) = iterate(c.ctx,i)
Base.iterate(c::Context,) = iterate(c.ctx)

abstract type JudgmentHead end
abstract type Constructor <: JudgmentHead end 
args(c::Constructor) = c.args

struct Judgment
  name::Name
  head::JudgmentHead
  ctx::Context
  Judgment(n,h,c=Context()) = new(n,h,c)
end

Base.:(==)(x::Judgment,y::Judgment) = x.head == y.head && x.ctx == y.ctx
Base.hash(x::Judgment, h) = hash(x.head, hash(x.ctx, h))
getname(j::Judgment) = j.name
rename(j::Judgment, n::Name) = Judgment(n, j.head, j.ctx)

# Args index the CONTEXT of the judgment
@struct_hash_equal struct TrmCon <: Constructor
  args::Vector{Lvl}
  typ::Typ
  function TrmCon(a,t)
    all(is_context, a) || error("Args for term constructor must refer to the context")
    return new(a,t)
  end
end

# Args index the CONTEXT of the judgment
@struct_hash_equal struct TypCon <: Constructor
  args::Vector{Lvl}
  function TypCon(a::AbstractVector{Lvl})
    all(is_context, a) || error("Args for type constructor must refer to the context")
    return new(a)
  end
end

arity(f::Constructor) = length(f.args)

@struct_hash_equal struct Axiom <: JudgmentHead
  typ::Typ
  equands::Vector{Trm}
  function Axiom(t,e)
    length(unique(e)) > 1 || error("Axiom must be nontrivial")
    return new(t,e)
  end
end

struct Theory
  name::Name
  judgments::Vector{Judgment}
end

Base.:(==)(x::Theory,y::Theory) = x.judgments == y.judgments
Base.hash(x::Theory, h) = hash(x.judgments, h)
Base.getindex(t::Theory,i::Lvl) = 
  is_context(i) ? error("Bad index $i") : t.judgments[index(i)]
Base.length(t::Theory) = t.judgments |> length
judgments(t::Theory) = t.judgments

"""
The full context for a `Trm` or `Typ` consists of both the list of judgments in
the theory, and also the list of judgments in the context.

TODO: maybe we should have different terms for "context judgment" and "theory
judgment"
"""
struct FullContext
  judgments::Vector{Judgment}
  context::Context
end

"""
Get the `Lvl` corresponding to a Name. This is the most recent judgment with
that name.
"""
function lookup(fc::FullContext, n::Name)
  i = findlast(nt -> nt[1] == n, fc.context.ctx)
  if !isnothing(i)
    return Lvl(i; context=true)
  end
  i = findlast(j -> j.name == n, fc.judgments)
  if !isnothing(i)
    Lvl(i; context=false)
  else
    throw(KeyError(n))
  end
end

lookup(fc::FullContext, s::Symbol) = lookup(fc, Name(s))

const empty_theory = Theory(Anon(), Judgment[])

"""
A type-level signifier for a particular theory, used to control dispatch
and to pass around theory objects (which can't be type parameters) at
the type level.

Structs which subtype `AbstractTheory` should always be singletons, and
have `theory` defined on them.
"""
abstract type AbstractTheory end

"""
Meant to be overloaded as

```julia
gettheory(::T) = ...
```

where `T` is a singleton struct subtyping `AbstractTheory`

Returns the @ref(Theory) associated to `T`.
"""
function gettheory end

"""
A convenience overload of `theory`
"""
gettheory(T::Type{<:AbstractTheory}) = gettheory(T())

struct ThEmpty <: AbstractTheory end

gettheory(::ThEmpty) = empty_theory

end
