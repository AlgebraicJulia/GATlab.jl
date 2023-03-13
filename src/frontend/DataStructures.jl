module DataStructures
export Name, Anon, Idx, TermCon, TypeCon, Trm, Typ, Axiom, Theory, Context, Judgment,
  extend, args, arity, ThEmpty, TheoryMap, Composite

using ...Util.Lists
using StructEquality

# Indexing
##########

const Idx = Int

# Terms
#######

abstract type InContext end # Trm, Typ

abstract type Name end
struct Literal <: Name 
  name::String 
end

Name(n::String) = Literal(n)
Name(n::Name) = n
Name(n::Symbol) = Literal(string(n))

struct Anon <: Name
end

const INTMIN = (;init=typemin(Int))

"""
head - indexes term constructors in an (implicit) theory
args - arguments that the term constructor is applied to
"""
@struct_hash_equal struct Trm <: InContext
  head::Idx # debruijn index into the term context
  args::Vector{Trm}
  Trm(h,a=Trm[]) = new(Idx(h),a)
end

@struct_hash_equal struct Typ <: InContext
  head::Idx # debruijn index into the type context
  args::Vector{Trm}
  Typ(h,a=Trm[]) = new(Idx(h),a)
end

head(t::InContext) = t.head
args(t::InContext) = t.args

# Judgments
############

abstract type JudgmentHead end
abstract type Constructor <: JudgmentHead end 

"""
name - just documentation (and for rendering)
"""
struct Judgment
  name::Name
  ctx::AbstractVector{Judgment}
  head::JudgmentHead
  Judgment(n,c,h) = new(Name(n),c,h)
end

Base.:(==)(x::Judgment, y::Judgment) = x.head == y.head && x.ctx == y.ctx 
Base.hash(x::Judgment, h::UInt64) = hash(x.ctx, hash(x.head, h))

Base.nameof(x::Judgment) = x.name

rename(x::Judgment, n::Name) = Judgment(n, x.ctx, x.head)

const Context = AbstractVector{Judgment}

"""
A type constructor

args - indexes the ctx. I.e. "1" refers to the first term constructor in the 
       codom of the context. This subset ought be sufficient to type infer every  
       constant introduced in the context.
"""
@struct_hash_equal struct TypeCon <: Constructor
  args::Vector{Idx}
  TypeCon(a=Idx[]) = new(a)
end

"""
A term constructor

typ  - output type of applying the term constructor
args - indexes the ctx.
"""
@struct_hash_equal struct TermCon <: Constructor
  typ::Typ
  args::Vector{Idx}
  TermCon(t,a=Idx[]) = new(t,a)
end

args(x::Constructor) = x.args
arity(x::Constructor) = length(args(x))

"""
equands - the things being equated 
"""
@struct_hash_equal struct Axiom <: JudgmentHead
  type::Typ
  equands::Vector{Trm}
  Axiom(t,ts) = new(t,ts)
end

ctx(x::Judgment) = x.ctx
name(x::Judgment) = x.name

# Theories
##########

"""
This returns the maximum index relative to the base of the context.

If this is positive, this means that the context is not closed.
"""
function maxind(c::Context)
  maximum(maxind(j) - i + 1 for (i,j) in enumerate(c); INTMIN...)
end

function maxind(j::Judgment)
  max(
    maxind(j.head) - length(j.ctx),
    maxind(j.ctx)
  )
end

function maxind(termcon::TermCon)
  max(
    maxind(termcon.typ),
    maximum(termcon.args; INTMIN...)
  )
end

maxind(typecon::TypeCon) = maximum(typecon.args; INTMIN...)

function maxind(axiom::Axiom)
  max(
    maxind(axiom.type),
    maximum(maxind.(axiom.equands); INTMIN...)
  )
end

maxind(t::InContext) = max(head(t), maximum(maxind.(args(t)); INTMIN...))

struct Theory 
  name::Name
  context::Context
  function Theory(n,context)
    maxind(context) <= 0 || error("Bad context: theory $n must be closed")
    return new(Name(n),context)
  end
end

Base.collect(t::Theory) = collect(t.context)
Base.length(t::Theory) = length(t.context)

function extend(t::Theory, n, js::AbstractVector{Judgment})
  Theory(
    n,
    vcat(t.context, js)
  )
end

const ThEmpty = Theory(Anon(), Bwd{Judgment}())

# TheoryMaps
############

"""
See documentation for TheoryMap.
"""
const Composite = Union{Trm, Typ, Nothing}

"""
A TheoryMap is a morphism between theories. Each judgment in the domain theory
is sent to a "composite" in the codomain.

I.e., each term constructor is sent to a term, each type constructor is sent to
a type, and each axiom is sent to nothing (the fact that the axioms are
preserved is a *property* of the mapping, not a structure, so we don't need to
write it down; we may need to find proofs later.)

The term that a term constructor is sent to a term in the context given by
"mapping over" the context of the term constructor using the previous judgment
mappings. This is a context extension of the codomain theory. So the deBruijn
indices in this term are implicitly relative to that context extension.

The same thing holds for type constructors.

The mapping from judgments to composites is implicit in the matching up of
`dom.context` with `composites`. I.e. the judgment at `dom.context[i]` is sent
to `composites[i]`.

The term/type at `composites[i]` has as an implicit context
`vcat(codom.context, |dom.context[i].ctx|)`
where `|Γ|` is the interpretation of the context `Γ` in `dom` in `codom` using
the TheoryMap, however this implicit context is not stored inside this
datastructure.

As this is a frontend datastructure, there is almost no consistency checking
here, and it is very possible to make a TheoryMap that makes no sense.
Additionally, preservation of equations is not at all checked here.
"""
struct TheoryMap
  dom::Theory
  codom::Theory
  composites::AbstractVector{Composite}
end

"""
Examples:

double = @theorymap ThNat -> ThNat begin
  ℕ => ℕ
  Z => Z
  S(n) => S(S(n))
end

double = TheoryMap(
  ThNat,
  ThNat,
  Bwd([
    Typ(3),
    Trm(2),
    Trm(2, [Trm(2, Trm(1))])
  ])
)

@theorymap ThCategory -> ThPreorder begin
  Ob => Ob
  Hom(a,b) => Leq(a,b)
  (f ⋅ g) => trans(f, g)
  id(a) => refl(a)
end
"""

end # module
