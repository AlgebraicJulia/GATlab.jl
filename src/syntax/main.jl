module Terms
export Lvl, is_theory, is_context, is_argument, index,
  TrmTyp, Trm, Typ, headof, argsof

"""
Thoughts on possible redesign:

Namespacing should be first class. This doesn't play nicely with deBruijn levels.

Possible redesign: each context/theory is associated with a UUID. A reference consists
of a UUID and a name. When we try and interpret a term, we check if the UUID matches
its parent context, and if it does not, we throw an error.

When we have a nested term, i.e. `a.b`, first `a` is looked up in the context that
we expect for `a`, and then `b` is looked up in the context for the struct type of `a`.

Then we use names everywhere instead of deBruijn levels. We overload term constructors
by desugaring into name + sort signature + UUID.
"""

"""
The tag of a Lvl takes up two bits and can be three things:

00: part of the theory
01: part of the context
10: part of the argument to a dependent context
"""
@struct_hash_equal struct Lvl
  val::UInt64
  function Lvl(i::Integer; context=false, argument=false)
    i > 0 || error("Creating non-positive level $i context $context")
    !(context && argument) || error("at most one of context and argument can be true")
    new(UInt64(i) | (UInt64(context) << 62) | (UInt64(argument) << 63))
  end
end

TAG_MASK = UInt64(3) << 62

tag(i::Lvl) = i.val >> 62

is_theory(i::Lvl) = tag(i) == 0

is_context(i::Lvl) = tag(i) == 1

is_argument(i::Lvl) = tag(i) == 2

index(i::Lvl) = Int(i.val & (~TAG_MASK))

Base.:(+)(i::Lvl, j::Int) = Lvl(i.val + UInt64(j))

abstract type TrmTyp end

headof(t::TrmTyp) = t.head
argsof(t::TrmTyp) = t.args

@struct_hash_equal struct Trm <:TrmTyp
  head::Lvl
  args::Vector{Trm}
  function Trm(l::Lvl, a=Trm[])
    is_theory(l) || isempty(a) || error("Elements of context are *nullary* term constructors")
    return new(l,a)
  end
  function Trm(l::Int, a=Trm[])
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
  function Typ(l, a=Lvl[])
    is_theory(l) || error("Bad head for type: $(index(l))")
    return new(l,a)
  end
end

struct ContextElt
  name::Name
  typ::Typ
end

Base.nameof(elt::ContextElt) = elt.name
typof(elt::ContextElt) = elt.typ

@struct_hash_equal struct Context
  pairs::Vector{ContextElt}
  Context(c=Tuple{Name, Typ}[]) = new(c)
end

Base.getindex(c::Context, i::Lvl) = is_context(i) ? c.pairs[index(i)] : error("$i")
Base.collect(c::Context) = collect(c.pairs)
Base.length(c::Context) = length(c.pairs)
Base.iterate(c::Context, i) = iterate(c.pairs,i)
Base.iterate(c::Context) = iterate(c.pairs)

end
